import { ICE, Id, Library, Range, ScamperError, Stmt } from './lang.js'
import { Env, Prog, Op, reservedWords, Value, } from './lang.js'
import { renderToHTML, mkCodeElement, mkSourceBlock, renderToOutput , renderToDraw } from './display.js'
import * as C from './contract.js'
import './styles.css'
import { makeList } from './docs/api/prelude.js'

let maxCallStackDepth = 100000;

///// Machine state structures /////////////////////////////////////////////////

class Control {
  idx: number
  ops: Op.T[]

  constructor (ops: Op.T[]) {
    this.idx = 0
    this.ops = ops
  }

  isEmpty (): boolean { return this.idx >= this.ops.length }
  next (): Op.T { return this.ops[this.idx++] }

  toString (): string {
    return `[idx=${this.idx}, ops=${this.ops.map(Op.toString).join(',')}]`
  }

  jumpTo(label: Op.Label): void {
    let cur = this.ops[this.idx]
    while (!this.isEmpty() && (cur.tag !== 'lbl' || cur.name !== label)) {
      cur = this.ops[++this.idx]
    }
    if (this.isEmpty()) {
      throw new ICE('Control.jumpTo', `Label ${label} not found`)
    }
  }
}

class ExecutionState {
  stack: Value.T[]
  env: Env
  control: Control
  dump: [Value.T[], Env, Control][]

  constructor (env: Env, ops: Op.T[]) {
    // N.B., if the state consists of a single value, then immediately
    // turn the value Op to a genuine value to avoid an unnecessary
    // step of computation
    if (ops.length === 1 && ops[0].tag === 'val') {
      this.stack = [ops[0].value]
      this.control = new Control([])
    } else {
      this.stack = []
      this.control = new Control(ops)
    }
    this.env = env
    this.dump = []
  }

  isFinished(): boolean { return this.control.isEmpty() && this.dump.length === 0 }

  dumpAndSwitch (stack: Value.T[], env: Env, ops: Op.T[], range?: Range): void {
    this.dump.push([this.stack, this.env, this.control])
    this.stack = stack
    this.env = env
    this.control = new Control(ops)
    if (this.dump.length > maxCallStackDepth) {
      throw new ScamperError('Runtime', "Maximum call stack size exceeded", undefined, range)
    }
  }

  isDumpEmpty() { return this.dump.length === 0 }

  popDump () {
    const [stack, env, control] = this.dump.pop()!
    this.stack = stack
    this.env = env
    this.control = control
  }

  jumpPast (label: Op.Label): void {
    this.control.jumpTo(label)
    this.control.idx += 1
  }

  public getBoundsEnv(libNum: number): [Id, Value.T][] | undefined {
    return this.env.toString2(libNum)
  }

  public getStack() {
    return this.stack
  }
}

///// Raising (ops to values) //////////////////////////////////////////////////

function findCondBranches (start: number, label: string, ops: Op.T[]): { branches: { guard: Op.T[], body: Op.T[] }[], endIdx: number } {
  let i = start
  const branches: { guard: Op.T[], body: Op.T[] }[] = []
  let guard: Op.T[] = []
  let op = ops[i]
  while (op.tag !== 'lbl' || op.name !== label) {
    if (op.tag === 'cond' && op.end === label) {
      branches.push({ guard, body: op. body})
      guard = []
    } else {
      guard.push(op)
    }
    op = ops[++i]
  }
  return { branches, endIdx: i }
}

function findArgs (start: number, label: string, ops: Op.T[]): { segments: Op.T[][], endIdx: number } {
  let i = start
  let segments: Op.T[][] = []
  let seg: Op.T[] = []
  let op = ops[i]
  while (op.tag !== 'lbl' || op.name !== label) {
    if ((op.tag === 'and' || op.tag === 'or') && op.jmpTo === label) {
      segments.push(seg)
      seg = []
    } else {
      seg.push(op)
    }
    op = ops[++i]
  }
  return { segments, endIdx: i }
}

function valToExp (v: Value.T): Value.T {
  if (Value.isNumber(v)) {
    return v
  } else if (Value.isBoolean(v)) {
    return v
  } else if (Value.isString(v)) {
    return v
  } else if (Value.isNull(v)) {
    return Value.mkSym('null')
  } else if (Value.isVoid(v)) {
    return v
  } else if (Value.isArray(v)) {
    return Value.vectorToList([
      Value.mkSym('vector'),
      ...(v as Value.T[]).map((v) => valToExp(v))
    ])
  } else if (Value.isClosure(v)) {
    const cls = v as Value.Closure
    if (cls.name === undefined) {
      return Value.vectorToList([
        Value.mkSym('lambda'),
        Value.vectorToList(cls.params.map((p) => Value.mkSym(p))),
        dumpToValue([[], cls.env, new Control(cls.ops)])
      ])
    } else {
      return Value.mkSym(cls.name)
    }
  } else if (Value.isJsFunction(v)) {
    return Value.mkSym((v as Function).name)
  } else if (Value.isChar(v)) {
    return v
  } else if (Value.isList(v)) {
    if (v === null) {
      return Value.mkSym('null')
    } else {
      const elems = Value.listToVector(v as Value.List)
      return Value.vectorToList([
        Value.mkSym('list'),
        ...elems.map((v) => valToExp(v))
      ])
    }
  } else if (Value.isPair(v)) {
    return Value.vectorToList([
      Value.mkSym('pair'),
      valToExp((v as Value.Pair).fst),
      valToExp((v as Value.Pair).snd)
    ])
  } else if (Value.isStruct(v)) {
    // TODO: problems! When raising a value to an expression, we rely on valToExp to
    // convert values to expression forms, in particular lists. This way, we know
    // the difference between a list value `(list + 2 3)` and a form `(+ 2 3)`.
    // However, in this case, our conversion is too early: display needs the original
    // struct value in order to custom render it. The hack is to simply return the
    // original struct value. However, now, any forms/lists nested inside of a
    // struct may be rendered incorrectly.
    //
    // One fix might be to take this "opToValue" pipeline in sem.ts and turn it into
    // an "opToHTML" pipeline so that we can properly integrate the special forms
    // checking into here. That's a bit of work to implement, so maybe we can get away
    // with a variant of the split architecture we have now. The right path is unclear...
    return v
    // const s = v as Value.Struct
    // const fields = Value.getFieldsOfStruct(s)
    // return Value.mkStruct(s[Value.structKind], fields, fields.map((f) => valToExp(s[f])))
  } else {
    // TODO: urk, when does this arise?
    return v
  }
}

function dumpToValue ([stack, env, control]: [Value.T[], Env, Control], hole?: Value.T): Value.T {
  let valStack = [...stack.map(valToExp)]
  if (hole !== undefined) { valStack.push(hole) }
  for (let i = control.idx; i < control.ops.length; i++) {
    const op = control.ops[i]
    if (op.tag === 'var') {
      if (env.has(op.name)) {
        const val = env.get(op.name)!
        if (Value.isClosure(val) || Value.isJsFunction(val)) {
          valStack.push(Value.mkSym(op.name))
        } else {
          valStack.push(env.get(op.name)!)
        }
      } else {
        valStack.push(Value.mkSym(op.name))
      }
    } else if (op.tag === 'val') {
      valStack.push(valToExp(op.value))
    } else if (op.tag === 'cls') {
      valStack.push(Value.vectorToList([
        Value.mkSym('lambda'),
        Value.vectorToList(op.params.map((p) => Value.mkSym(p))),
        dumpToValue([[], env, new Control(op.ops)])
      ])) 
    } else if (op.tag === 'ap') {
      const args = op.arity === 0 ? [] : valStack.slice(-op.arity)
      for (let i = 0; i < op.arity; i++) { valStack.pop() }
      valStack.push(Value.vectorToList([
        valStack.pop()!,
        ...args
      ]))
    } else if (op.tag === 'if') {
      const elseb = dumpToValue([[], env, new Control(op.elseb)])
      const ifb = dumpToValue([[], env, new Control(op.ifb)])
      const guard = valStack.pop()!
      valStack.push(Value.vectorToList([
        Value.mkSym('if'),
        guard,
        ifb,
        elseb
      ]))
    } else if (op.tag === 'let') {
      const names = op.names
      const bindings = names.reverse().map((n: string) =>
        ({ name: n, body: valStack.pop()! })).reverse()
      // N.B., names bound by the let shadow outer bindings, so remove them
      // from the environment so that we don't replace them by accident!
      const body = dumpToValue([[], env.quotient(...names), new Control(op.body)])
      valStack.push(Value.vectorToList([
        Value.mkSym('let'),
        Value.vectorToList(bindings.map((b) => [Value.mkSym(b.name), b.body])),
        body
      ]))
    } else if (op.tag === 'seq') {
      if (op.numSubexps === 0) {
        valStack.push(Value.vectorToList([Value.mkSym('begin')]))
      } else {
        const exps = valStack.slice(-op.numSubexps)
        for (let i = 0; i < op.numSubexps; i++) { valStack.pop() }
        valStack.push(Value.vectorToList([
          Value.mkSym('begin'),
          ...exps
        ]))
      }
    } else if (op.tag === 'match') {
      const scrutinee = valStack.pop()!
      const branches = op.branches.map((b) => [
        b.pattern,
        dumpToValue([[], env, new Control(b.body)])
      ])
      valStack.push(Value.vectorToList([
        Value.mkSym('match'),
        scrutinee,
        Value.vectorToList(branches)
      ])) 

    } else if (op.tag === 'and') {
      const { segments, endIdx } = findArgs(i + 1, op.jmpTo, control.ops)
      const args = [valStack.pop()!].concat(segments.map((ops) => dumpToValue([[], env, new Control(ops)])))
      valStack.push(Value.vectorToList([
        Value.mkSym('and'),
        ...args
      ]))
      i = endIdx
    } else if (op.tag === 'or') {
      const { segments, endIdx } = findArgs(i + 1, op.jmpTo, control.ops)
      const args = [valStack.pop()!].concat(segments.map((ops) => dumpToValue([[], env, new Control(ops)])))
      valStack.push(Value.vectorToList([
        Value.mkSym('or'),
        ...args
      ]))
      i = endIdx
    } else if (op.tag === 'cond') {
      const first = [valStack.pop()!, dumpToValue([[], env, new Control(op.body)])]
      const { branches, endIdx } = findCondBranches(i + 1, op.end, control.ops)
      valStack.push(Value.vectorToList([
        Value.mkSym('cond'),
        Value.vectorToList([first].concat(branches.map((b) => [
          dumpToValue([[], env, new Control(b.guard)]),
          dumpToValue([[], env, new Control(b.body)])
        ])))
      ]))
      i = endIdx
    } else if (op.tag === 'exn') {
      valStack.push(Value.vectorToList([
        Value.mkSym('error'),
        op.msg
      ]))
    } else if (op.tag === 'lbl') {
      // N.B., do nothing, skip over labels!
    }
  }
  if (valStack.length !== 1) {
    throw new ICE('sem.dumpToExp', `Stack size is not 1 after execution: ${stack}`)
  } else {
    return valStack.pop()!
  }
}

export function opsToValue (ops: Op.T[]): Value.T {
  return dumpToValue([[], new Env([]), new Control(ops)])
}

export function stateToExp (state: ExecutionState): Value.T | undefined {
  const dump: [Value.T[], Env, Control][] = [...state.dump]
  dump.push([state.stack, state.env, state.control])
  let ret: Value.T | undefined = undefined
  for (let i = dump.length - 1; i >= 0; i--) {
    ret = dumpToValue(dump[i], ret)
  }
  return ret
}

///// Evaluation ///////////////////////////////////////////////////////////////

function assertNotReserved (ident: string): void {
  if (reservedWords.includes(ident)) {
    throw new ScamperError('Runtime', `"${ident}" is a reserved word and cannot be used as an identifier`, undefined)
  }
}

export function tryMatch (p: Value.T, v: Value.T, range?: Range): [string, Value.T][] | undefined {
  if (Value.isSymName(p, '_')) {
    return []
  } else if (Value.isSym(p)) {
    const s = p as Value.Sym
    assertNotReserved(s.value)
    return [[s.value, v]]
  } else if (p === null && v === null) {
    return []
  } else if (typeof p === 'boolean' && typeof v === 'boolean' && p === v) {
    return []
  } else if (typeof p === 'number' && typeof v === 'number' && p === v) {
    return []
  } else if (typeof p === 'string' && typeof v === 'string' && p === v) {
    return []
  } else if (Value.isChar(p) && Value.isChar(v)) {
    return (p as Value.Char).value === (v as Value.Char).value ? [] : undefined
  } else if (p === null && v === null) {
    return []
  } else if (Value.isPair(p) && (Value.isPair(v) || Value.isStruct(v))) {
    const elems = Value.listToVector(p as Value.List)
    // N.B., performed a null check above, so p has at least one element
    const head = elems[0]
    const args = elems.slice(1)
    if (!Value.isSym(head)) {
      throw new ScamperError('Runtime', 'A symbol is expected at the head of a constructor pattern', undefined, range)
    }
    const ctor = (head as Value.Sym).value
    if ((ctor === 'pair' || ctor === 'cons') && args.length === 2 && Value.isPair(v)) {
      const env1 = tryMatch(args[0], (v as Value.Pair).fst)
      const env2 = tryMatch(args[1], (v as Value.Pair).snd)
      return env1 && env2 ? env1.concat(env2) : undefined
  } else if (Value.isStructKind(v, ctor)) {
      const st = v as Value.Struct
      const fields = Value.getFieldsOfStruct(st)
      if (fields.length === args.length) {
        let env: [string, Value.T][] = []
        for (let i = 0; i < fields.length; i++) {
          const env2 = tryMatch(args[i], st[fields[i]])
          if (!env2) {
            return undefined
          }
          env = env.concat(env2)
        }
        return env
      } else {
        return undefined
      }
    }
  } else {
    return undefined
  }
}



function stepPrim (state: ExecutionState): boolean {
  const op = state.control.next()
  const stack = state.stack
  switch (op.tag) {

    case 'val': {
      stack.push(op.value)
      return true
    }

    case 'cls': {
      stack.push(Value.mkClosure(op.params.length, op.params, op.ops, state.env))
      return true
    }
  
    case 'var': {
      assertNotReserved(op.name)
      if (state.env.has(op.name)) {
        stack.push(state.env.get(op.name)!)
      } else {
        throw new ScamperError('Runtime', `Referenced unbound identifier "${op.name}".`, undefined, op.range)
      }
      return true
    }

    case 'ap': {
      if (stack.length < op.arity + 1) {
        throw new ICE('sem.step', `Not enough arguments on stack. Need ${op.arity + 1}, have ${stack.length}`)
      }
      const head = stack[stack.length - op.arity - 1]
      const args = op.arity === 0 ? [] : stack.slice(-op.arity)
      for (let i = 0; i < op.arity + 1; i++) { stack.pop() }
      if (Value.isClosure(head)) {
        const closure = head as Value.Closure
        if (closure.params.length !== args.length) {
          throw new ScamperError('Runtime', `Function expected ${closure.params.length} arguments, passed ${args.length} instead.`, undefined, op.range)
        } else {
          const env = closure.env.extend(closure.params.map((p, i) => [p, args[i]]))
          const ops = closure.ops
          const range = op.range
          // N.B., if the control is empty, then we can tail-call optimize by
          // overwriting the current state instead of dumping.
          if (state.control.isEmpty()) {
            state.stack = []
            state.env = env
            state.control = new Control(closure.ops)
          } else {
            state.dumpAndSwitch([], env, ops, range)
          }
        }
        return false
      } else if (Value.isJsFunction(head)) {
        const fn = head as Function
        try {
          const result = fn(...args) as Value.T
          stack.push(result)
        } catch (e) {
          // N.B., annotate any errors from foreign function calls with
          // range information from this application
          if (e instanceof ScamperError) {
            e.source = fn.name
            e.range = op.range
          }
          throw e
        }
        // N.B., continue stepping if we step through one of the primitive
        // constructor-functions
        return fn.name === 'pair' || fn.name === 'list' || fn.name === 'vector'
      } else {
        throw new ScamperError('Runtime', `Non-function value (${Value.typeOf(head)}) in function application`, undefined, op.range)
      }
    }

    case 'if': {
      if (stack.length >= 1) {
        const guard = stack.pop()!
        if (guard === true) {
          state.dumpAndSwitch([], state.env, op.ifb, op.range)
        } else if (guard === false) {
          state.dumpAndSwitch([], state.env, op.elseb, op.range)
        } else {
          throw new ScamperError('Runtime', `Boolean expected in conditional, received ${Value.toString(guard)} instead`, undefined, op.range)
        }
      } else {
        throw new ICE('sem.step', `Guard missing from stack for conditional`)
      }
      return false
    }

    case 'let': {
      op.names.forEach(assertNotReserved)
      if (stack.length >= op.names.length) {
        const values = stack.slice(-op.names.length)
        for (let i = 0; i < op.names.length; i++) {
          stack.pop()
        }
        const newEnv = state.env.extend(op.names.map((n, i) => [n, values[i]]))
        state.dumpAndSwitch([], newEnv, op.body)
      } else {
        throw new ICE('sem.step', `Not enough values on stack for let binding`)
      }
      return false
    }
  
    case 'seq': {
      stack.slice(-op.numSubexps)
      if (stack.length >= op.numSubexps) {
        // N.B., the top of the stack is the last value created which we want to return!
        const ret = stack.pop()
        for (let i = 1; i < op.numSubexps; i++) { stack.pop() }
        stack.push(ret)
      } else {
        throw new ICE('sem.step', `Not enough values on stack for sequence, ${op.numSubexps} expected, ${stack.length} found`)
      }
      return false
    }
  
    case 'match': {
      if (stack.length >= 1) {
        const scrutinee = stack.pop()!
        let foundMatch = false
        for (let i = 0; !foundMatch && i < op.branches.length; i++) {
          const bindings = tryMatch(op.branches[i].pattern, scrutinee)
          if (bindings) {
            state.dumpAndSwitch([], state.env.extend(bindings), op.branches[i].body, op.range)
            foundMatch = true
          }
        }
        if (!foundMatch) {
          throw new ScamperError('Runtime', `No pattern matches for ${Value.toString(scrutinee)}`, undefined, op.range)
        }
      } else {
        throw new ICE('sem.step', `Scrutinee missing from stack for match`)
      }
      return false
    }

    case 'and': {
      if (stack.length < 1) {
        throw new ICE('sem.and', 'Missing argument to "and" instruction')
      }
      const val = stack.pop()!
      if (typeof val !== 'boolean') {
        throw new ScamperError('Runtime', `"and" expects a boolean value, received ${Value.typeOf(val)}`, undefined, op.range)
      }
      if (!val) {
        state.stack.push(false)
        state.jumpPast(op.jmpTo)
      }
      // N.B., otherwise, move onto the next instruction!
      return false
    }

    case 'or': {
      if (stack.length < 1) {
        throw new ICE('sem.or', 'Missing argument to "or" instruction')
      }
      const val = stack.pop()!
      if (typeof val !== 'boolean') {
        throw new ScamperError('Runtime', `"or" expects a boolean value, received ${Value.typeOf(val)}`, undefined, op.range)
      }
      if (val) {
        state.stack.push(true)
        state.jumpPast(op.jmpTo)
      }
      // N.B., otherwise, move onto the next instruction!
      return false
    }
    
    case 'cond': {
      if (stack.length < 1) {
        throw new ICE('sem.cond', 'Missing guard to "cond" instruction')
      }
      const guard = stack.pop()!
      if (guard) {
        // N.B., make sure to switch this frame's instr pointer before jumping
        // otherwise we'll forget where to return to!
        state.jumpPast(op.end)
        state.dumpAndSwitch([], state.env, op.body, op.range)
      }
      return false
    }

    case 'lbl': {
      // N.B., skip over a label peacefully
      return true
    }

    case 'exn': {
      throw new ScamperError('Runtime', op.msg, op.modName, op.range, op.source)
    }
  }
}

function step (state: ExecutionState): void {
  var cont = false
  do {
    cont = stepPrim(state)
    // N.B., pop the dump until we arrive at a non-finished state
    while (state.control.isEmpty() && !state.isDumpEmpty()) {
      const ret = state.stack.pop()!
      state.popDump()
      state.stack.push(ret)
    }
  } while (!state.isFinished() && cont)
}

function executeStructDecl (name: string, fields: string[], env: Env): Env {
  assertNotReserved(name)
  fields.forEach(assertNotReserved)
  const predFn = function (v: any) {
    C.checkContract(arguments, C.contract(`${name}?`, [C.any]))
    return Value.isStructKind(v, name)
  }
  Value.nameFn(`${name}?`, predFn)
  const pred: [string, Value.T] = [`${name}?`, predFn]

  const ctorFn = function (...args: any[]) {
    C.checkContract(arguments, C.contract(name, fields.map((_f) => C.any)))
    return Value.mkStruct(name, fields, args)
  }
  Value.nameFn(name, ctorFn)
  const ctor: [string, Value.T] = [name, ctorFn]

  const fieldFns: [string, Value.T][] = []
  fields.forEach((f) => {
    const fieldName = `${name}-${f}`
    const fn = function (v: Value.Struct) {
      C.checkContract(arguments, C.contract(fieldName, [C.struct(name)]))
      return v[f]
    }
    Value.nameFn(fieldName, fn)
    fieldFns.push([fieldName, fn])
  })

  return env.extend([pred, ctor, ...fieldFns])
}

function execute (state: ExecutionState): Value.T {
  while (!state.isFinished()) {
    step(state)
  }
  if (state.stack.length !== 1) {
    throw new ICE('sem.execute', `Stack size is not 1 after execution: ${state.stack}`)
  }
  return state.stack.pop()!
}

function runClosure (closure: Value.Closure, ...args: Value.T[]): Value.T {
  const state = new ExecutionState(closure.env.extend(closure.params.map((x, i) => [x, args[i]])), closure.ops)
  return execute(state)
}

export function callFunction (fn: Value.Closure | Function, ...args: any): any {
  if (Value.isClosure(fn)) {
    return runClosure(fn as Value.Closure, ...args)
  } else {
    return (fn as Function)(...args)
  }
}

function makeTraceDiv(): HTMLElement {
  const div = document.createElement('div')
  div.classList.add('scamper-trace')
  return div
}

function makeTraceHeader (s: Stmt.T): HTMLElement {
  switch (s.kind) {
    case 'binding': {
      const ret = mkCodeElement(`Evaluating binding ${s.name}...`)
      ret.append(mkCodeElement('\n'))
      ret.append(renderToHTML(opsToValue(s.body)))
      return ret
    }

    case 'display': {
      const ret = mkCodeElement('Evaluating displayed expression...')
      ret.append(mkCodeElement('\n'))
      ret.append(renderToHTML(opsToValue(s.body)))
      return ret
    }

    case 'import':
      return mkCodeElement(`Importing module ${s.modName}...`)

    case 'exp': {
      const ret = mkCodeElement('Evaluating expression...')
      ret.append(mkCodeElement('\n'))
      ret.append(renderToHTML(opsToValue(s.body)))
      return ret
    }

    case 'struct':
      return mkCodeElement(`Evaluating struct declaration ${s.id}...`)
  }
}


function vectorHeight(vec: any, index: number = 0): number {
  let height = 1;
  for(let i = index; i < vec.length; i++) {
    let e = vec[i]
    if(typeof e === 'string' || typeof e === 'number' || typeof e === 'boolean') {
      height = height + 1
    } else if(Value.isPair(e)) {
      if(e.isList) {
        height = height + listHeight(e) + 1
      } else {
        height = height + 1
      }
    } else if(Value.typeOf(e) === 'vector') {
      height = height + vectorHeight(e, 0) + 1
    }
  }
  return height + 3
}

function drawVector(vector: any): any {
  let str = ''
  vector.forEach((e: any) => {
    if(typeof e === 'string' || typeof e === 'number' || typeof e === 'boolean') {
      str = str + '[' + e + ']'
    } else if (Value.isPair(e)) {
      if(e.isList) {
        str = str + '[' + drawList(e) + ']'
      } else {
        str = str + '[' +  drawPair(e) + ']'
      }
    } else if (Value.typeOf(e) === 'vector') {
      str = str + '[' + drawVector(e) + ']'
    }
  })

  return str
}

function drawVectorHTML(vector: any): any {
  //Container for html elements
  let div = document.createElement('div');
  div.ariaLabel = 'object type vector';
  div.tabIndex = 0;
  div.style.position = 'relative';

  //loops through the vector, making the visualization pieces for each element
  vector.forEach((e: any, i: number) => {
    //container for all the html elements for one vector element
    const col = document.createElement('div');
    col.className = 'vector-style';
    if (i > 0) col.style.position = 'absolute'
    col.style.left = `${30 * vector.indexOf(e)}px`
    //col.style.top = '20px'

    //creates the elements for the box elements of the vector
    const box = document.createElement('div');
    const index = document.createElement('div');
    const indexVal = vector.indexOf(e).toString();
    index.className = 'index-box';
    index.textContent = indexVal;
    col.appendChild(index);
    box.className = 'vector-box';
    //box.role = 'img'
    box.tabIndex = 0;
    box.ariaDescription = `vector index ${indexVal} contains ${'' + e}`
    box.ariaLabel = `vector index ${indexVal} contains ${'' + e}`
    col.appendChild(box);

    //creates the arrow element for the vector
    for(let j=0; j < vectorHeight(vector, i + 1) - 3; j++) {
      const arrow = document.createElement('div');
      arrow.className = 'vec-arrow'
      col.appendChild(arrow);
    }

    const val = document.createElement('div');
    val.className = 'val-box';
    val.textContent = '▼\n';
    col.appendChild(val);
    let val2 = document.createElement('div');
    val2.className = 'val-box';
    //creates the box containing the value in the element
    if(typeof e === 'string' || typeof e === 'number' || typeof e === 'boolean') {
      val2.textContent = e + '';
      col.appendChild(val2);
    } else if (Value.isPair(e)) {
      if(e.isList) {
        col.appendChild(drawListHTML(e));
      } else {
        col.appendChild(drawPair(e));
      }
    } else if (Value.typeOf(e) === 'vector') {
      col.appendChild(drawVectorHTML(e));
    }
     div.appendChild(col);
  })
  

  return div
}

function lengthList(lst: any, count: number = 0) {
  if(lst.snd === null) {
    return count + 1
  } else {
    count = count + 1
    return lengthList(lst.snd, count)
  }
}

function drawList(list: any): any {
  if(list.isList) {
    let str = '{ '
    let val = list.fst
    let next = list.snd
    if(typeof val === 'string' || typeof val === 'number' || typeof val === 'boolean') {
    //  console.log(val)
      str = str + val + ''
    } else if (Value.isPair(val)) {
      if(val.isList) {
        str = str + drawList(val)
      } else {
        str = str + drawPair(val) + ''
      }
    } else if (Value.typeOf(val) === 'vector') {
      str = str + drawVector(val) + ''
    }
    if(next === null) {
      return str + ' }{ /}'
    } else {
      return str = str + ' }{ -}-> ' + drawList(next)
    }
    
  }
}


function listHeight(list: any): number {
  let height = 0
  if(list.isList) {
    const fst = list.fst
    if(list.snd === null) {
      if(typeof fst === 'string' || typeof fst === 'number' || typeof fst === 'boolean') {
        height = height + 1 + 1
      } else if(Value.isPair(fst)) {
        if(fst.isList) {
          height = height + listHeight(fst) + 1
        } else {
          height = height + 3 + 1
        }
      } else if(Value.typeOf(fst) === 'vector') {
        height = height + vectorHeight(fst) + 1
      }
    } else {
      const next = list.snd.fst;
      if(typeof fst === 'string' || typeof fst === 'number' || typeof fst === 'boolean') {
        height = height + 1 + listHeight(list.snd)
      } else if(Value.isPair(fst)) {
        if(fst.isList) {
          height = height + 1 + listHeight(fst) + listHeight(list.snd)
        } else {
          height = height + 1 + listHeight(list.snd)
        }
      } else if(Value.typeOf(fst) === 'vector') {
        height = height + vectorHeight(fst) + listHeight(list.snd)
      }
    }
  }
  return height + 2
}

// function listLooper(list: any, count: number = 0): number {
//   let len = lengthList(list);
//   for(let i = 0; i < len!; i++) {
//     if(list.fst.isList) {
//       //please for the love of god don't forget the mindspace for this
//       count += lengthList(list.fst);
//       count += listLooper(list.fst);
//     }
//   }
//   return count;
// }

// function drawListAlt(list: any) {
//   //declares overall html object to be appended to page
//   const div = document.createElement('div');
//   div.ariaDescription = 'object type list';
//   div.tabIndex = 0;
//   let elemArr: any[] = [];

//   if(list.isList) {
//     let len = lengthList(list);

//     //loops through the list creating pairs and arrows for each element
//     for(let i = 0; i < len!; i++) {
//       //creates the container for the individual list element and the sub element that contains the list pair
//       const col = document.createElement('div');
//       col.className = 'vector-style';
//       const top = document.createElement('div');
//       top.className = 'list-style'

//       //creates the list pair elements
//       for(let j = 0; j < 2; j++) {
//         const box = document.createElement('div');
//         box.tabIndex = 0;
//         if(j === 0) {
//           box.ariaDescription = `list pair ${i}, first element contains ${list.fst}`;
//           box.ariaLabel = `list pair ${i}, first element contains ${list.fst}`;
//         } else {
//           box.ariaDescription = `list pair ${i}, second element contains a list pair`;
//           box.ariaLabel = `list pair ${i}, second element contains a list pair`;
//         }
//         if(i === len!-1 && j === 1) {
//           box.className = 'null-box';
//           box.ariaDescription = `list pair ${i}, second element contains null`;
//           box.ariaLabel = `list pair ${i}, second element contains null`;
//         } else {
//           box.className = 'list-box';
//         }
//         top.appendChild(box);
//       }

//       //creates the arrow pointing to the next list element, if there is one
//       if(i !== len! - 1) {
//         const nextArrow = document.createElement('div');
//         nextArrow.className = 'list-arrow';
//         const arrowHead = document.createElement('div');
//         arrowHead.className = 'arrow-box'
//         arrowHead.textContent = '▶'
//         top.appendChild(nextArrow);
//         top.appendChild(arrowHead);
//       }
//       col.appendChild(top);

//       //creates the arrow pointing to the contained element
//       for(let j = 0; j < len! - i; j++) {
//         const arrow = document.createElement('div');
//         arrow.className = 'list-arrow-down'
//         col.appendChild(arrow);
//       }

//       //creates the box containing the value in the element
//       const val = document.createElement('div');
//       val.className = 'val-box';
//       val.textContent = '▼\n' + list.fst;
//       col.appendChild(val);
      
//       //iterates the list
//       list = list.snd;
//       div.appendChild(col);
//     }
//   }
//   return div;
// }

function drawListHTML(list: any): any {
  //declares overall html object to be appended to page
  const div = document.createElement('div');
  div.ariaDescription = 'object type list';
  div.tabIndex = 0;

  if(list.isList) {
    let len = lengthList(list);

    //loops through the list creating pairs and arrows for each element
    for(let i = 0; i < len!; i++) {
      //creates the container for the individual list element and the sub element that contains the list pair
      const col = document.createElement('div');
      col.className = 'vector-style';
      const top = document.createElement('div');
      top.className = 'list-style'

      //creates the list pair elements
      for(let j = 0; j < 2; j++) {
        const box = document.createElement('div');
        box.tabIndex = 0;
        if(j === 0) {
          box.ariaDescription = `list pair ${i}, first element contains ${list.fst}`;
          box.ariaLabel = `list pair ${i}, first element contains ${list.fst}`;
        } else {
          box.ariaDescription = `list pair ${i}, second element contains a list pair`;
          box.ariaLabel = `list pair ${i}, second element contains a list pair`;
        }
        if(i === len!-1 && j === 1) {
          box.className = 'null-box';
          box.ariaDescription = `list pair ${i}, second element contains null`;
          box.ariaLabel = `list pair ${i}, second element contains null`;
        } else {
          box.className = 'list-box';
        }
        top.appendChild(box);
      }

      //creates the arrow pointing to the next list element, if there is one
      if(i !== len! - 1) {
        const nextArrow = document.createElement('div');
        nextArrow.className = 'list-arrow';
        const arrowHead = document.createElement('div');
        arrowHead.className = 'arrow-box'
        arrowHead.textContent = '▶'
        top.appendChild(nextArrow);
        top.appendChild(arrowHead);
      }
      col.appendChild(top);

      if(list.snd !== null) {
        //creates the arrow pointing to the contained element
        for(let j = 0; j < listHeight(list.snd); j++) {
          const arrow = document.createElement('div');
          arrow.className = 'list-arrow-down'
          col.appendChild(arrow);
        }
      } else {
        const arrow = document.createElement('div');
        arrow.className = 'list-arrow-down'
        col.appendChild(arrow);
      }
        
      let el = list.fst
      const val = document.createElement('div');
      val.className = 'val-box';
      val.textContent = '▼\n'
      col.appendChild(val);
      const val2 = document.createElement('div');
      val2.className = 'val-box';
      //creates the box containing the value in the element
      if(typeof el === 'string' || typeof el === 'number' || typeof el === 'boolean') {
        val2.textContent = el + ''
        col.appendChild(val2);
      } else if (Value.isPair(el)) {
        if(el.isList) {
          col.appendChild(drawListHTML(el));
        } else {
          col.appendChild(drawPair(el));
        }
      } else if (Value.typeOf(el) === 'vector') {
        col.appendChild(drawVectorHTML(el));
      }
      
      //iterates the list
      list = list.snd;
      div.appendChild(col);
    }
  }
  return div;
}

function drawPair(pair: any): any {
  let str = ''
  let fst = pair.fst
  let snd = pair.snd
  if(typeof fst === 'string' || typeof fst === 'number' || typeof fst === 'boolean') {
    str = str + '{ ' + fst
  } else if(Value.isPair(fst)) {
    str = str + drawPair(fst) + ' }'
  } else if(Value.typeOf(fst) === 'list') {
    str = str + drawList(fst) + ' }'
  }
  str = str + ' }-{ '
  if(typeof snd === 'string' || typeof snd === 'number' || typeof snd === 'boolean') {
    str = str + snd + ' }'
  } else if(Value.isPair(snd)) {
    str = str + drawPair(snd) + ' }'
  } else if(Value.typeOf(snd) === 'list') {
    str = str + drawList(snd) + ' }'
  }
  return str
}

function drawPairHTML(pair: any): any {

}

export class Sem {
  display: HTMLElement
  env: Env
  prog: Prog
  src: string
  curStmt: number
  state?: ExecutionState
  builtinLibs: Map<Id, Library>
  traces?: HTMLElement[]
  defaultDisplay: boolean
  isPrintingCode: boolean
  isDrawing: boolean

  constructor (display: HTMLElement,
               builtinLibs: Map<Id, Library>,
               isTracing: boolean,
               isDrawing: boolean,
               defaultDisplay: boolean,
               isPrintingCode: boolean,
               env: Env,
               prog: Prog,
               src: string) {
    this.display = display
    this.builtinLibs = builtinLibs
    this.isDrawing = isDrawing
    if (isTracing || isDrawing) {
      this.traces = new Array(prog.length)
      for (let i = 0; i < prog.length; i++) {
        this.traces[i] = makeTraceDiv()
      }
    } else {
      this.traces = undefined
    }
    this.env = env
    this.prog = prog
    this.src = src
    // N.B., start at -1 so that we can advance immediately
    this.curStmt = -1
    this.state = undefined
    this.defaultDisplay = defaultDisplay
    this.isPrintingCode = isPrintingCode
    this.advance()
  }

  isFinished (): boolean { return this.curStmt === this.prog.length }
  isTracing (): boolean { return this.traces !== undefined }
  //isDrawing(): boolean { return this}
  appendToCurrentTrace (v: HTMLElement | string): void {
    if (typeof v === 'string') {
      v = mkCodeElement(v)
    }
    this.traces![this.curStmt]!.appendChild(v)
  }

  advance (): void {
    this.curStmt += 1
    this.state = undefined
    if (!this.isFinished() && this.isTracing()) {
      this.display.appendChild(this.traces![this.curStmt]!)
      this.appendToCurrentTrace(makeTraceHeader(this.prog[this.curStmt]))
      this.appendToCurrentTrace('\n')
    }
  }

  tryPrintCurrentCodeSegment(): void {
    if (this.isPrintingCode) {
      const start        = this.curStmt === 0 ? 0 : this.prog[this.curStmt - 1].range.end.idx + 1
      const end          = this.prog[this.curStmt].range.end.idx + 1
      const seg          = this.src.substring(start, end)
      const renderedCode = mkSourceBlock(seg.trim())
      this.display.appendChild(renderedCode)
    }
  }

  stepDefine (name: string, body: Op.T[], range: Range): void {
    if (this.state === undefined) {
      assertNotReserved(name)
      this.tryPrintCurrentCodeSegment()
      this.state = new ExecutionState(this.env, body)
    }
    if (!this.state.isFinished()) {
      try {
        step(this.state)
        if (this.isTracing()) {
          this.appendToCurrentTrace('-->')
          this.appendToCurrentTrace(' ')
          this.appendToCurrentTrace(renderToHTML(stateToExp(this.state)!))
          this.appendToCurrentTrace('\n')
          
        }
      } catch (e) {
        renderToOutput(this.display, e)
        this.advance()
        if(this.isDrawing) {this.draw()}
      }
    } else {
      if (this.state.stack.length !== 1) {
        throw new ICE('sem.step', `Stack size is not 1 after execution: ${this.state.stack}`)
      }
      // N.B., if we bind a lambda, annotate the closure value with the
      // name for stepping purposes
      const val = this.state.stack.pop()!
      if (Value.isClosure(val)) {
        (val as Value.Closure).name = name
      }
      if (this.env.has(name)) {
        throw new ScamperError('Runtime', `Identifier "${name}" already bound`, undefined, range)
      } else {
        this.env.set(name, val)
        
      }
      if(this.isDrawing) {
        this.draw()
      }
      if (this.isTracing()) {
        this.appendToCurrentTrace(mkCodeElement(`${name} bound`))
      }
      this.advance()
    }
  }

  stepImport (modName: string, range: Range): void {
    this.tryPrintCurrentCodeSegment()
    if (this.builtinLibs.has(modName)) {
      const library = this.builtinLibs.get(modName)!
      this.env = this.env.extend(library.lib)
      if (library.initializer !== undefined) {
        library.initializer()
      }
      if (this.isTracing()) {
        this.appendToCurrentTrace(`Module ${modName} imported`)
      }
      this.advance()
    } else {
      this.advance()
      throw new ScamperError('Runtime', `Module ${modName} not found`, undefined, range)
    }
  }

  stepStruct (id: string, fields: string[]): void {
    this.tryPrintCurrentCodeSegment()
    this.env = executeStructDecl(id, fields, this.env)
    if (this.isTracing()) {
      this.appendToCurrentTrace(`Struct ${id} declared`)
      
    }
    this.advance()
  }

  stepDisplay (body: Op.T[], _range?: Range): void {
    if (this.state === undefined) {
      this.tryPrintCurrentCodeSegment()
      this.state = new ExecutionState(this.env, body)
    }
    if (!this.state.isFinished()) {
      try {
        step(this.state)
        if (this.isTracing()) {
          this.appendToCurrentTrace('-->')
          this.appendToCurrentTrace(' ')
          this.appendToCurrentTrace(renderToHTML(stateToExp(this.state)!))
          this.appendToCurrentTrace('\n')
        }
      } catch (e) {
        renderToOutput(this.display, e)
        this.advance()
      }
    } else {
      if (this.state.stack.length !== 1) {
        throw new ICE('sem.step', `Stack size is not 1 after execution: ${this.state.stack}`)
      }
      renderToOutput(this.display, valToExp(this.state.stack.pop()))
      this.advance()
    }
  }

  stepExp (body: Op.T[]): void {
    if (this.state === undefined) {
      this.tryPrintCurrentCodeSegment()
      this.state = new ExecutionState(this.env, (body))
    }
    if (!this.state.isFinished()) {
      try {
        step(this.state)
        if (this.isTracing()) {
          this.appendToCurrentTrace('-->')
          this.appendToCurrentTrace(' ')
          this.appendToCurrentTrace(renderToHTML(stateToExp(this.state)!))
          this.appendToCurrentTrace('\n')
        }
      } catch (e) {
        renderToOutput(this.display, e)
        this.advance()
      }
    } else {
      if (this.state.stack.length !== 1) {
        throw new ICE('sem.step', `Stack size is not 1 after execution: ${this.state.stack}`)
      }
      const value: Value.T = this.state.stack.pop()!
      if (value !== null && typeof value === 'object' &&
        value.hasOwnProperty(Value.scamperTag) &&
        (value as any)[Value.scamperTag] === 'set-maximum-recursion-depth') {
          maxCallStackDepth = (value as any)['value']
      } else if (this.defaultDisplay) {
        renderToOutput(this.display, valToExp(value))
      }
      this.advance()
    }
  }

  step (): void {
    let stmt = this.prog[this.curStmt]
    switch (stmt.kind) {
      case 'binding':
        this.stepDefine(stmt.name, stmt.body, stmt.range)
        break
      case 'exp':
        this.stepExp(stmt.body)
        break
      case 'import':
        this.stepImport(stmt.modName, stmt.range)
        break
      case 'display':
        this.stepDisplay(stmt.body, stmt.range)
        break
      case 'struct':
        this.stepStruct(stmt.id, stmt.fields)
        break
    }
  }

  stepToNextStmt (): void {
    const idx = this.curStmt
    try {
      while (!this.isFinished() && this.curStmt === idx) { this.step() }
    } catch (e) {
      renderToOutput(this.display, e)
    }
  }

  execute (): void {
    try {
      while (!this.isFinished()) { this.step() }
    } catch (e) {
      renderToOutput(this.display, e)
    }
  }

  draw (): void {
    let envState = this.state
    let initialLibNum = 0

    this.builtinLibs.forEach(l => {
      initialLibNum += l.lib.length
    })

    if(envState != undefined){
      let bounded = envState.getBoundsEnv(initialLibNum)
      let stack = envState.getStack()

      if(!stack[0]) {
        if(bounded != undefined && bounded.length > 0) {
          renderToDraw(this.display, "------------------------------~")

          bounded?.forEach(e => {
            let strVal: any = e[1]?.toString()
            let HTMLVal: any = ''

            if(strVal != undefined) {
              if(typeof e[1] === 'string' && typeof e[0] === 'number' && typeof stack[0] != 'boolean') {
                strVal = strVal
                HTMLVal = '-'
              } else if (e[1] != undefined && Value.typeOf(e[1]) === 'vector') {
                strVal = drawVector(e[1]) + ' Vetcor Height ' + (vectorHeight(e[1]) + 1)
                HTMLVal = drawVectorHTML(e[1])
              } else if (e[1] != undefined && Value.typeOf(e[1]) === 'list') {
                strVal = drawList(e[1]) + ' List Height == ' + (listHeight(e[1]) + 1)
                HTMLVal = drawListHTML(e[1])
              } else if (e[1] != undefined && Value.isPair(e[1])) {
                strVal = drawPair(e[1])
              } else if (e[1] != undefined && Value.isFunction(e[1])) {
                strVal = ("PROCEDURE")
              } else {
                strVal
              }
              
            renderToDraw(this.display, e[0] + "  --->  " + strVal)
            renderToDraw(this.display, HTMLVal)
            }
          })
          renderToDraw(this.display, "------------------------------^")
        }
      }

      let stackString;
      let stackHTML;

      if(stack[0]) {
        stackString = stack[stack.length - 1]?.toString()
        console.log(stack[0])
        console.log(stackString)
        if(typeof stack[0] != 'string' && typeof stack[0] != 'number' && typeof stack[0] != 'boolean') {
          if(stack[0] != undefined && Value.typeOf(stack[0]) === 'vector') {
            stackString = drawVector(stack[0])
            stackHTML = drawVectorHTML(stack[0])
          } else if (stack[0] != undefined && Value.typeOf(stack[0]) === 'list') {
            stackString = drawList(stack[0])
            stackHTML = drawListHTML(stack[0])
          } else if (stack[0] != undefined && Value.isPair(stack[0])) {
            stackString = drawPair(stack[0])
          } else if (stack[0] != undefined && Value.isFunction(stack[0])) {
            if(stack[0].name) {
              if(stack[0].name === 'cons') {
                let last: any = stack[stack.length - 1]
                if(last.snd === null) {
                  stackString = drawList(Value.mkList(last.fst))
                  stackHTML = drawListHTML(Value.mkList(last.fst))
                } else if(last.snd.isList) {
                  stackString = drawList(Value.mkPair(last.fst, last.snd))
                  stackHTML = drawListHTML(Value.mkPair(last.fst, last.snd))
                } else {
                  stackString = drawPair(Value.mkPair(last.fst, last.snd))
                }
              } else if(stack[0].name === 'map') {
                //forEachstack.push(Value.mkList)
                console.log("mapping")
              }
            } else {
              stackString = ("PROCEDURE")
            }
          }
        }
        renderToDraw(this.display,  ">>> " + stackString)
        renderToDraw(this.display, stackHTML)
      }
    }
  }
}