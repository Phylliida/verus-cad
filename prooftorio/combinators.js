/* combinators.js — BCKW mode: variable-free computation.
 *
 * - Turner bracket abstraction: compiles lambda terms to combinators
 *   {S,K,I,B,C,W}; the B/C/eta optimizations keep output near-linear
 *   (naive S,K-only abstraction is quadratic and unreadable).
 * - Reduction: local rewrite rules only — no substitution, no renaming:
 *     I x → x      K x y → x        S f g x → f x (g x)
 *     B f g x → f (g x)   C f x y → f y x   W f x → f x x
 * - Principal type inference (Damas–Milner without let): Curry-style,
 *   so *untyped* combinator terms get their most general type inferred.
 *   The types of the combinators are exactly Hilbert's axioms:
 *     K : a → b → a     S : (a → b → c) → (a → b) → a → c
 */
(function () {
'use strict';
const L = (typeof module !== 'undefined') ? require('./lambda.js') : window.LambdaCore;
const { App, Var } = L;

const ARITY = { I: 1, K: 2, S: 3, B: 3, C: 3, W: 2 };
const isComb = n => Object.prototype.hasOwnProperty.call(ARITY, n);

// ---------- reduction ----------
function spineArgs(t) {
  const a = [];
  while (t.tag === 'app') { a.push(t.arg); t = t.fn; }
  return { head: t, args: a.reverse() };
}
function rebuild(h, args) { let t = h; for (const a of args) t = App(t, a); return t; }

function combRedex(name, args) {
  const n = ARITY[name];
  if (args.length < n) return null;
  const [a0, a1, a2] = args, rest = args.slice(n);
  let r;
  switch (name) {
    case 'I': r = a0; break;
    case 'K': r = a0; break;
    case 'S': r = App(App(a0, a2), App(a1, a2)); break;
    case 'B': r = App(a0, App(a1, a2)); break;
    case 'C': r = App(App(a0, a2), a1); break;
    case 'W': r = App(App(a0, a1), a1); break;
  }
  return rebuild(r, rest);
}

// normal-order step: head redex first, then left-to-right; delta-unfolds defs
function stepComb(t, env) {
  switch (t.tag) {
    case 'var': { const d = env[t.name]; return d && d.value ? d.value : null; }
    case 'app': {
      const { head, args } = spineArgs(t);
      if (head.tag === 'var' && isComb(head.name)) {
        const r = combRedex(head.name, args);
        if (r) return r;
      }
      const f = stepComb(t.fn, env); if (f) return App(f, t.arg);
      const a = stepComb(t.arg, env); if (a) return App(t.fn, a);
      return null;
    }
    case 'lam': { // shouldn't appear after compilation; reduce inside just in case
      const b = stepComb(t.body, env); return b ? { ...t, body: b } : null;
    }
    default: return null;
  }
}

function normalizeComb(t, env, cap = 1000) {
  let n = 0;
  while (n < cap) {
    const s = stepComb(t, env);
    if (!s) return { term: t, steps: n, capped: false };
    t = s; n++;
  }
  return { term: t, steps: n, capped: true };
}

// ---------- Turner bracket abstraction ----------
// [x] t  =  combinator term with x eliminated, such that ([x] t) x ⟶* t
function bracket(x, t) {
  if (!L.freeVars(t).has(x)) return App(Var('K'), t);   // x unused: constant
  if (t.tag === 'var') return Var('I');                  // t is x itself
  if (t.tag === 'app') {
    const a = t.fn, b = t.arg;
    const fa = L.freeVars(a).has(x), fb = L.freeVars(b).has(x);
    if (!fa && b.tag === 'var' && b.name === x) return a; // eta: [x](a x) = a
    if (!fa) return App(App(Var('B'), a), bracket(x, b)); // B a g x = a (g x)
    if (!fb) return App(App(Var('C'), bracket(x, a)), b); // C f b x = f x b
    return App(App(Var('S'), bracket(x, a)), bracket(x, b));
  }
  throw { message: 'bracket abstraction: unexpected ' + t.tag };
}

function compile(t) {
  switch (t.tag) {
    case 'lam': return bracket(t.param, compile(t.body));
    case 'app': return App(compile(t.fn), compile(t.arg));
    case 'var': return t;
    default: throw { message: `combinator mode: '${t.tag}' terms can't be compiled (lambda terms only)` };
  }
}

function size(t) {
  switch (t.tag) {
    case 'var': case 'star': case 'box': return 1;
    case 'app': return 1 + size(t.fn) + size(t.arg);
    case 'lam': return 1 + (t.annot ? size(t.annot) : 0) + size(t.body);
    case 'pi': return 1 + size(t.annot) + size(t.body);
  }
  return 1;
}

// ---------- principal type inference ----------
let tvc = 0;
const TVar = () => ({ tag: 'tvar', id: ++tvc });
const TArr = (a, b) => ({ tag: 'tarr', a, b });

const COMB_TYPES = {
  I: () => { const a = TVar(); return TArr(a, a); },
  K: () => { const a = TVar(), b = TVar(); return TArr(a, TArr(b, a)); },
  S: () => { const a = TVar(), b = TVar(), c = TVar(); return TArr(TArr(a, TArr(b, c)), TArr(TArr(a, b), TArr(a, c))); },
  B: () => { const a = TVar(), b = TVar(), c = TVar(); return TArr(TArr(b, c), TArr(TArr(a, b), TArr(a, c))); },
  C: () => { const a = TVar(), b = TVar(), c = TVar(); return TArr(TArr(a, TArr(b, c)), TArr(b, TArr(a, c))); },
  W: () => { const a = TVar(), b = TVar(); return TArr(TArr(a, TArr(a, b)), TArr(a, b)); },
};

function applyT(sub, t) {
  if (t.tag === 'tvar') {
    for (const s of sub) if (s.id === t.id) return applyT(sub, s.type);
    return t;
  }
  return TArr(applyT(sub, t.a), applyT(sub, t.b));
}

function occurs(sub, id, t) {
  t = applyT(sub, t);
  if (t.tag === 'tvar') return t.id === id;
  return occurs(sub, id, t.a) || occurs(sub, id, t.b);
}

function unify(sub, a, b) {
  a = applyT(sub, a); b = applyT(sub, b);
  if (a.tag === 'tvar') {
    if (b.tag === 'tvar' && a.id === b.id) return sub;
    if (occurs(sub, a.id, b)) throw { message: 'occurs check failed — this term would need an infinite type (it is not typable)' };
    sub.push({ id: a.id, type: b });
    return sub;
  }
  if (b.tag === 'tvar') return unify(sub, b, a);
  unify(sub, a.a, b.a);
  unify(sub, a.b, b.b);
  return sub;
}

function tvarsOf(t, acc = new Set()) {
  if (t.tag === 'tvar') acc.add(t.id);
  else { tvarsOf(t.a, acc); tvarsOf(t.b, acc); }
  return acc;
}

// freshen exactly the quantified variables of a definition's scheme
function instantiate(t, qids) {
  const m = new Map();
  const go = t => {
    if (t.tag === 'tvar') {
      if (!qids.has(t.id)) return t;
      if (!m.has(t.id)) m.set(t.id, TVar());
      return m.get(t.id);
    }
    return TArr(go(t.a), go(t.b));
  };
  return go(t);
}

// ctx: {sub, defs: name->type (scheme), qids: name->Set, mono: name->type, monoIds: Set}
function inferT(ctx, t) {
  if (t.tag === 'var') {
    if (isComb(t.name)) return COMB_TYPES[t.name]();
    if (ctx.defs[t.name]) return instantiate(ctx.defs[t.name], ctx.qids[t.name]);
    if (!ctx.mono[t.name]) { ctx.mono[t.name] = TVar(); ctx.monoIds.add(ctx.mono[t.name].id); }
    return ctx.mono[t.name];
  }
  if (t.tag === 'app') {
    const tf = inferT(ctx, t.fn), ta = inferT(ctx, t.arg), r = TVar();
    unify(ctx.sub, tf, TArr(ta, r));
    return applyT(ctx.sub, r);
  }
  throw { message: 'type inference: unexpected ' + t.tag };
}

const LETTERS = 'abcdefghijklmnopqrstuvwxyz';
function showType(t, sub) {
  if (sub) t = applyT(sub, t);
  const names = new Map(); let n = 0;
  const nm = id => {
    if (!names.has(id)) { names.set(id, n < 26 ? LETTERS[n] : 't' + (n - 25)); n++; }
    return names.get(id);
  };
  const go = (t, ctx) => {
    if (t.tag === 'tvar') return nm(t.id);
    const s = go(t.a, 1) + ' → ' + go(t.b, 0);
    return ctx > 0 ? '(' + s + ')' : s;
  };
  return go(t, 0);
}

// Compile + infer a whole program. Definitions are compiled once, generalized,
// and later uses reference them by name (sharing — nothing is inlined).
function inferProgram(prog) {
  const ctx = { sub: [], defs: {}, qids: {}, mono: {}, monoIds: new Set() };
  const env = {};
  const lines = [];
  let lamSize = 0, combSize = 0;
  for (const d of prog.defs) {
    if (d.kind === 'axiom') throw { message: `combinator mode: no 'axiom' needed — types are inferred; free constants just get fresh type variables` };
    if (isComb(d.name)) throw { message: `'${d.name}' is a primitive combinator in this mode — pick another name` };
    const c = compile(d.value);
    const ty = applyT(ctx.sub, inferT(ctx, c));
    ctx.defs[d.name] = ty;
    ctx.qids[d.name] = new Set([...tvarsOf(ty)].filter(id => !ctx.monoIds.has(id)));
    env[d.name] = { value: c };
    lines.push({ name: d.name, type: ty, compiled: c });
    lamSize += size(d.value); combSize += size(c);
  }
  let finalType = null, finalCompiled = null;
  if (prog.final) {
    finalCompiled = compile(prog.final);
    finalType = applyT(ctx.sub, inferT(ctx, finalCompiled));
    lamSize += size(prog.final); combSize += size(finalCompiled);
  }
  return { lines, finalType, finalCompiled, env, lamSize, combSize, sub: ctx.sub };
}

function compileProgram(src) { return inferProgram(L.parse(src)); }

const Comb = {
  ARITY, isComb, stepComb, normalizeComb, bracket, compile, size,
  inferT, inferProgram, compileProgram, showType, unify, TVar, TArr,
};
if (typeof module !== 'undefined') module.exports = Comb;
if (typeof window !== 'undefined') window.Comb = Comb;
})();
