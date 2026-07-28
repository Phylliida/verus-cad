/* machine.js — CEK machine: evaluation with environments, no substitution.
 *
 * State = (control, env, kont). A lambda evaluates to a *closure* pairing its
 * code with the current environment; application extends the closure's env.
 * Variables are dictionary lookups. Nothing is ever renamed or substituted —
 * this is how real interpreters work, and arguably the intuitive semantics
 * that beta-reduction obscures.
 *
 * kont frames: arg(term,env) = "evaluate me next, I'm the argument"
 *              fun(value)    = "I'm the function, waiting for its argument"
 */
(function () {
'use strict';
const L = (typeof module !== 'undefined') ? require('./lambda.js') : window.LambdaCore;

// env: assoc list {name, value, parent} | null;  value: {tag:'closure', lam, env}
function lookup(name, env, globals) {
  for (let e = env; e; e = e.parent) if (e.name === name) return e.value;
  if (Object.prototype.hasOwnProperty.call(globals, name)) return globals[name];
  return undefined;
}

function cekStep(st) {
  if (st.done || st.stuck) return st;
  st = { ...st, steps: st.steps + 1 };
  if (!st.isValue) {
    const c = st.control;
    if (c.tag === 'var') {
      const v = lookup(c.name, st.env, st.globals);
      if (v === undefined) return { ...st, stuck: `no value for '${c.name}' (free variable)` };
      return { ...st, control: v, isValue: true };
    }
    if (c.tag === 'lam') return { ...st, control: { tag: 'closure', lam: c, env: st.env }, isValue: true };
    if (c.tag === 'app') return { ...st, control: c.fn, kont: { tag: 'arg', term: c.arg, env: st.env, next: st.kont } };
    return { ...st, stuck: `cannot evaluate a '${c.tag}' term` };
  }
  const v = st.control, k = st.kont;
  if (k === null) return { ...st, done: true };
  if (k.tag === 'arg') return { ...st, control: k.term, env: k.env, kont: { tag: 'fun', value: v, next: k.next }, isValue: false };
  const f = k.value; // fun frame: apply the function value to v
  if (f.tag !== 'closure') return { ...st, stuck: 'tried to apply a non-function value' };
  return { ...st, control: f.lam.body, env: { name: f.lam.param, value: v, parent: f.env }, kont: k.next, isValue: false };
}

function cekRun(st, cap = 1000) {
  while (st.steps < cap && !st.done && !st.stuck) st = cekStep(st);
  return st;
}

// Build the initial state: evaluate each definition to a value first
// (sharing: defs are evaluated once, later uses point at the same value).
function cekInit(src) {
  const p = L.evalProgram(src);
  const globals = {};
  for (const d of p.prog.defs) {
    if (d.kind === 'axiom') throw { message: `CEK mode: axiom '${d.name}' has no value to evaluate` };
    const r = cekRun({ control: d.value, env: null, kont: null, isValue: false, globals, steps: 0 });
    if (!r.done) throw { message: `CEK mode: definition '${d.name}' didn't produce a value${r.stuck ? ': ' + r.stuck : ' (step cap)'}` };
    globals[d.name] = r.control;
  }
  return { control: p.final, env: null, kont: null, isValue: false, globals, steps: 0 };
}

// ---------- display ----------
function flattenEnv(env) {
  const out = [], seen = new Set();
  for (let e = env; e; e = e.parent) {
    if (!seen.has(e.name)) { seen.add(e.name); out.push([e.name, e.value]); }
  }
  return out;
}

function showValue(v, depth = 1) {
  if (v.tag === 'closure') {
    let s = '«' + L.show(v.lam);
    if (depth > 0 && v.env) {
      const binds = flattenEnv(v.env);
      if (binds.length) s += ' | ' + binds.map(([n, val]) => n + '↦' + showValue(val, 0)).join(', ');
    }
    return s + '»';
  }
  return String(v);
}

function cekShow(st) {
  const lines = [];
  const g = Object.keys(st.globals);
  if (g.length) lines.push('globals: ' + g.join(', '));
  lines.push((st.done ? 'value:   ' : 'control: ') + (st.isValue ? showValue(st.control) : L.show(st.control)));
  const binds = flattenEnv(st.env);
  lines.push('env:     ' + (binds.length ? binds.map(([n, v]) => n + '↦' + showValue(v, 0)).join(', ') : '∅'));
  const frames = [];
  for (let k = st.kont; k; k = k.next) frames.push(k.tag);
  lines.push('kont:    ' + (frames.length ? frames.join(' · ') + ' · □' : '□'));
  if (st.stuck) lines.push('STUCK: ' + st.stuck);
  if (st.done) lines.push(`DONE — ${st.steps} machine steps`);
  return lines.join('\n');
}

const Machine = { cekStep, cekRun, cekInit, cekShow, showValue };
if (typeof module !== 'undefined') module.exports = Machine;
if (typeof window !== 'undefined') window.Machine = Machine;
})();
