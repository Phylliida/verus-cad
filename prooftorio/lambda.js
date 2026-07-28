/* lambda.js — core engine for the lambda cube playground.
 *
 * A generic Pure Type System (PTS) with two sorts ⋆ and □, axiom ⋆ : □,
 * and a parameterized rule set. The three axes of Barendregt's cube are
 * toggles that each add one formation rule:
 *
 *   always:   (⋆,⋆)   ordinary functions
 *   poly:     (□,⋆)   terms may depend on types   (System F polymorphism)
 *   typeops:  (□,□)   types may depend on types   (type operators, Fω)
 *   dep:      (⋆,□)   types may depend on terms   (dependent types, λP)
 *
 * Environment-agnostic: works as a browser global (LambdaCore) and in node.
 */
(function () {
'use strict';

// ---------- AST ----------
const Star = () => ({ tag: 'star' });
const Box  = () => ({ tag: 'box' });
const Var  = (name) => ({ tag: 'var', name });
const App  = (fn, arg) => ({ tag: 'app', fn, arg });
const Lam  = (param, annot, body) => ({ tag: 'lam', param, annot, body }); // annot null = untyped
const Pi   = (param, annot, body) => ({ tag: 'pi', param, annot, body });

// ---------- tokenizer ----------
const RESERVED = new Set(['axiom', 'Pi', 'forall', '_']);

function tokenize(src) {
  const toks = [];
  let i = 0, line = 1, col = 1;
  const isIdStart = c => /[A-Za-z_]/.test(c);
  const isId = c => /[A-Za-z0-9_']/.test(c);
  while (i < src.length) {
    const c = src[i];
    if (c === '\n') { line++; col = 1; i++; continue; }
    if (c === ' ' || c === '\t' || c === '\r') { i++; col++; continue; }
    if (c === '/' && src[i + 1] === '/') { while (i < src.length && src[i] !== '\n') i++; continue; }
    const at = { line, col };
    const two = src.slice(i, i + 2);
    if (two === ':=') { toks.push({ k: 'punct', v: ':=', ...at }); i += 2; col += 2; continue; }
    if (two === '->') { toks.push({ k: 'punct', v: '→', ...at }); i += 2; col += 2; continue; }
    if (two === '[]') { toks.push({ k: 'punct', v: '□', ...at }); i += 2; col += 2; continue; }
    if (c === '\\') { toks.push({ k: 'punct', v: 'λ', ...at }); i++; col++; continue; }
    if (c === '*')  { toks.push({ k: 'punct', v: '⋆', ...at }); i++; col++; continue; }
    if ('().:;λΠ∀→⋆□'.includes(c)) { toks.push({ k: 'punct', v: c, ...at }); i++; col++; continue; }
    if (isIdStart(c)) {
      let j = i;
      while (j < src.length && isId(src[j])) j++;
      toks.push({ k: 'ident', v: src.slice(i, j), ...at });
      col += j - i; i = j; continue;
    }
    throw { message: `unexpected character '${c}'`, line, col };
  }
  toks.push({ k: 'eof', v: '', line, col });
  return toks;
}

// ---------- parser ----------
// program  := (def ';')* expr?
// def      := 'axiom' IDENT ':' term | IDENT (':' term)? ':=' term
// term     := 'λ' binders '.' term | 'Π' binders '.' term | app ('→' term)?
// binders  := (IDENT+ (':' term)? | '(' IDENT+ ':' term ')')+
// app      := atom+
// atom     := IDENT | '⋆' | '□' | '(' term ')'
function parse(src) {
  const toks = tokenize(src);
  let p = 0;
  const peek = (n = 0) => toks[p + n];
  const next = () => toks[p++];
  const err = (message, t) => { throw { message, line: t.line, col: t.col }; };
  const expect = (v) => {
    const t = next();
    if (t.v !== v) err(`expected '${v}', got '${t.v === '' ? 'end of input' : t.v}'`, t);
    return t;
  };
  const isLamTok = t => t.v === 'λ';
  const isPiTok = t => t.v === 'Π' || t.v === '∀' || (t.k === 'ident' && (t.v === 'Pi' || t.v === 'forall'));
  const isIdent = t => t.k === 'ident' && !RESERVED.has(t.v);

  function parseIdents() {
    const names = [];
    while (isIdent(peek())) names.push(next().v);
    if (names.length === 0) err(`expected a variable name, got '${peek().v}'`, peek());
    if (names.includes('_')) err(`'_' is reserved`, peek());
    return names;
  }

  function parseAtom() {
    const t = peek();
    if (isIdent(t)) { next(); return Var(t.v); }
    if (t.k === 'ident') err(`'${t.v}' is a reserved word`, t);
    if (t.v === '⋆') { next(); return Star(); }
    if (t.v === '□') { next(); return Box(); }
    if (t.v === '(') { next(); const e = parseTerm(); expect(')'); return e; }
    err(`expected a term, got '${t.v === '' ? 'end of input' : t.v}'`, t);
  }

  const startsAtom = t => isIdent(t) || t.v === '(' || t.v === '⋆' || t.v === '□';

  function parseApp() {
    let t = parseAtom();
    while (startsAtom(peek())) t = App(t, parseAtom());
    return t;
  }

  function parseBinders() {
    const groups = [];
    while (true) {
      const t = peek();
      if (t.v === '(') {
        next();
        const names = parseIdents();
        expect(':');
        const annot = parseTerm();
        expect(')');
        groups.push({ names, annot });
        continue;
      }
      if (isIdent(t)) {
        const names = parseIdents();
        let annot = null;
        if (peek().v === ':') { next(); annot = parseTerm(); }
        groups.push({ names, annot });
        continue;
      }
      break;
    }
    if (groups.length === 0) err(`expected binder(s) after '${peek(-1) ? '' : ''}λ/Π'`, peek());
    return groups;
  }

  function parseTerm() {
    if (isLamTok(peek()) || isPiTok(peek())) {
      const isLam = isLamTok(next());
      const groups = parseBinders();
      expect('.');
      let body = parseTerm();
      // fold binder groups into nested lams/pis, innermost last
      for (let gi = groups.length - 1; gi >= 0; gi--) {
        const g = groups[gi];
        for (let ni = g.names.length - 1; ni >= 0; ni--) {
          body = isLam ? Lam(g.names[ni], g.annot, body) : Pi(g.names[ni], g.annot, body);
        }
      }
      return body;
    }
    const t = parseApp();
    if (peek().v === '→') {
      next();
      const rhs = parseTerm();
      return Pi('_', t, rhs); // non-dependent arrow; '_' never occurs free in rhs
    }
    return t;
  }

  function parseDef() {
    if (peek().k === 'ident' && peek().v === 'axiom') {
      next();
      const name = next();
      if (!isIdent(name)) err(`expected a name after 'axiom'`, name);
      expect(':');
      const type = parseTerm();
      return { kind: 'axiom', name: name.v, type };
    }
    const name = next().v; // caller verified lookahead
    let annot = null;
    if (peek().v === ':') { next(); annot = parseTerm(); }
    expect(':=');
    const value = parseTerm();
    return { kind: 'def', name, annot, value };
  }

  const defs = [];
  while (true) {
    const t = peek();
    if (t.k === 'eof') break;
    if (t.k === 'ident' && t.v === 'axiom') { defs.push(parseDef()); }
    else if (isIdent(t) && (peek(1).v === ':=' || peek(1).v === ':')) { defs.push(parseDef()); }
    else break;
    if (peek().v === ';') { next(); }
    else if (peek().k !== 'eof') err(`expected ';' after definition, got '${peek().v}'`, peek());
  }
  let final = null;
  if (peek().k !== 'eof') {
    final = parseTerm();
    if (peek().k !== 'eof') err(`unexpected '${peek().v}' after expression`, peek());
  }
  return { defs, final };
}

// ---------- free variables & substitution ----------
function freeVars(t, bound = new Set(), acc = new Set()) {
  switch (t.tag) {
    case 'var': if (!bound.has(t.name)) acc.add(t.name); break;
    case 'app': freeVars(t.fn, bound, acc); freeVars(t.arg, bound, acc); break;
    case 'lam':
    case 'pi': {
      if (t.annot) freeVars(t.annot, bound, acc);
      const b2 = new Set(bound); b2.add(t.param);
      freeVars(t.body, b2, acc);
      break;
    }
  }
  return acc;
}

let freshCtr = 0; // '#' cannot appear in source identifiers, so fresh names never collide

function subst(t, name, rep) {
  switch (t.tag) {
    case 'star': case 'box': return t;
    case 'var': return t.name === name ? rep : t;
    case 'app': return App(subst(t.fn, name, rep), subst(t.arg, name, rep));
    case 'lam':
    case 'pi': {
      const annot = t.annot ? subst(t.annot, name, rep) : null;
      if (t.param === name) return { tag: t.tag, param: t.param, annot, body: t.body };
      if (freeVars(rep).has(t.param)) {
        // capture-avoiding: rename the binder to a fresh name first
        const fresh = t.param + '#' + (++freshCtr);
        const renamed = subst(t.body, t.param, Var(fresh));
        return { tag: t.tag, param: fresh, annot, body: subst(renamed, name, rep) };
      }
      return { tag: t.tag, param: t.param, annot, body: subst(t.body, name, rep) };
    }
  }
}

// ---------- beta/delta reduction ----------
// env: name -> {type, value}; delta-unfolds definitions (value !== null).
// Normal-order (leftmost-outermost) single step. Returns null at normal form.
function step(t, env) {
  switch (t.tag) {
    case 'star': case 'box': return null;
    case 'var': {
      const d = env[t.name];
      return d && d.value ? d.value : null;
    }
    case 'app': {
      if (t.fn.tag === 'lam') return subst(t.fn.body, t.fn.param, t.arg);
      const f = step(t.fn, env); if (f) return App(f, t.arg);
      const a = step(t.arg, env); if (a) return App(t.fn, a);
      return null;
    }
    case 'lam': {
      if (t.annot) { const an = step(t.annot, env); if (an) return Lam(t.param, an, t.body); }
      const b = step(t.body, env); return b ? Lam(t.param, t.annot, b) : null;
    }
    case 'pi': {
      const an = step(t.annot, env); if (an) return Pi(t.param, an, t.body);
      const b = step(t.body, env); return b ? Pi(t.param, t.annot, b) : null;
    }
  }
}

function normalize(t, env, cap = 1000) {
  let n = 0;
  while (n < cap) {
    const s = step(t, env);
    if (s === null) return { term: t, steps: n, capped: false };
    t = s; n++;
  }
  return { term: t, steps: n, capped: true };
}

// weak head normal form: reduce only at the head
function whnf(t, env) {
  while (true) {
    if (t.tag === 'app') {
      const f = whnf(t.fn, env);
      if (f.tag === 'lam') { t = subst(f.body, f.param, t.arg); continue; }
      return App(f, t.arg);
    }
    if (t.tag === 'var') {
      const d = env[t.name];
      if (d && d.value) { t = d.value; continue; }
    }
    return t;
  }
}

// ---------- alpha equivalence (via de Bruijn depth comparison) ----------
function alphaEq(a, b, ea = [], eb = []) {
  if (a.tag !== b.tag) return false;
  switch (a.tag) {
    case 'star': case 'box': return true;
    case 'var': {
      const ia = ea.lastIndexOf(a.name), ib = eb.lastIndexOf(b.name);
      if (ia === -1 || ib === -1) return ia === -1 && ib === -1 && a.name === b.name;
      return ea.length - ia === eb.length - ib;
    }
    case 'app': return alphaEq(a.fn, b.fn, ea, eb) && alphaEq(a.arg, b.arg, ea, eb);
    case 'lam': case 'pi': {
      if ((a.annot === null) !== (b.annot === null)) return false;
      if (a.annot && !alphaEq(a.annot, b.annot, ea, eb)) return false;
      return alphaEq(a.body, b.body, [...ea, a.param], [...eb, b.param]);
    }
  }
}

// beta-delta convertibility: normalize both sides, compare up to alpha
function conv(a, b, env) {
  const na = normalize(a, env, 10000);
  const nb = normalize(b, env, 10000);
  return alphaEq(na.term, nb.term);
}

// ---------- pretty printer ----------
// freshened binders (x#3, made during capture-avoiding substitution) display
// with subscripts (x₃) so they stay visually distinct from source names
const SUBS = '₀₁₂₃₄₅₆₇₈₉';
const dispName = n => n.replace(/#(\d+)$/, (_, d) => [...d].map(c => SUBS[+c]).join(''));

function show(t, ctx = 0) {
  switch (t.tag) {
    case 'star': return '⋆';
    case 'box': return '□';
    case 'var': return dispName(t.name);
    case 'app': {
      const s = show(t.fn, 20) + ' ' + show(t.arg, 21);
      return ctx > 20 ? '(' + s + ')' : s;
    }
    case 'lam': {
      const parts = []; let cur = t;
      while (cur.tag === 'lam') {
        parts.push(cur.annot ? dispName(cur.param) + ':' + show(cur.annot) : dispName(cur.param));
        cur = cur.body;
      }
      const s = 'λ' + parts.join(' ') + '. ' + show(cur, 0);
      return ctx > 10 ? '(' + s + ')' : s;
    }
    case 'pi': {
      if (!freeVars(t.body).has(t.param)) { // non-dependent: arrow sugar
        const s = show(t.annot, 11) + ' → ' + show(t.body, 10);
        return ctx > 10 ? '(' + s + ')' : s;
      }
      const parts = []; let cur = t;
      while (cur.tag === 'pi' && freeVars(cur.body).has(cur.param)) {
        parts.push('(' + dispName(cur.param) + ':' + show(cur.annot) + ')');
        cur = cur.body;
      }
      const s = 'Π' + parts.join(' ') + '. ' + show(cur, 0);
      return ctx > 10 ? '(' + s + ')' : s;
    }
  }
}

// ---------- PTS typechecker ----------
// rules: {poly, typeops, dep} — booleans for the three cube axes.

const AXIS_INFO = {
  'box,star':  { label: 'polymorphism',    desc: 'terms depending on types (rule □,⋆)' },
  'box,box':   { label: 'type operators',  desc: 'types depending on types (rule □,□)' },
  'star,box':  { label: 'dependent types', desc: 'types depending on terms (rule ⋆,□)' },
};

function ruleAllowed(s1, s2, rules) {
  if (s1 === 'star' && s2 === 'star') return true;
  if (s1 === 'box' && s2 === 'star') return rules.poly;
  if (s1 === 'box' && s2 === 'box') return rules.typeops;
  if (s1 === 'star' && s2 === 'box') return rules.dep;
  return false;
}

function requireRule(s1, s2, rules, what) {
  if (ruleAllowed(s1, s2, rules)) return;
  const info = AXIS_INFO[`${s1},${s2}`];
  throw { message: `${what} needs ${info.desc} — enable the '${info.label}' toggle in the sidebar` };
}

const isSort = t => t.tag === 'star' || t.tag === 'box';

// infer(ctx, t, env, rules) -> type of t; ctx is a list of {name, type}
function infer(ctx, t, env, rules) {
  switch (t.tag) {
    case 'star': return Box();
    case 'box': throw { message: '□ is the top sort — it has no type' };
    case 'var': {
      for (let i = ctx.length - 1; i >= 0; i--) if (ctx[i].name === t.name) return ctx[i].type;
      const d = env[t.name];
      if (d && d.type) return d.type;
      throw { message: `unbound variable '${dispName(t.name)}'` };
    }
    case 'app': {
      const tf = whnf(infer(ctx, t.fn, env, rules), env);
      if (tf.tag !== 'pi') {
        throw { message: `cannot apply: ${show(t.fn)} has type ${show(tf)}, which is not a function type` };
      }
      const ta = infer(ctx, t.arg, env, rules);
      if (!conv(ta, tf.annot, env)) {
        throw { message: `type mismatch in application:\n  expected: ${show(tf.annot)}\n  got:      ${show(ta)}\n  in: ${show(t.fn)} applied to ${show(t.arg)}` };
      }
      return subst(tf.body, tf.param, t.arg);
    }
    case 'lam': {
      if (!t.annot) {
        throw { message: `unannotated binder 'λ${t.param}.' — untyped terms can't be typechecked (Church-style systems need λ${t.param}:SomeType. …)`, code: 'untyped' };
      }
      const s1 = infer(ctx, t.annot, env, rules);
      if (!isSort(s1)) throw { message: `binder annotation ${show(t.annot)} must be a type, but it has type ${show(s1)}` };
      const ctx2 = [...ctx, { name: t.param, type: t.annot }];
      const tb = infer(ctx2, t.body, env, rules);
      const s2 = infer(ctx2, tb, env, rules);
      if (!isSort(s2)) throw { message: `the type of the body, ${show(tb)}, is not itself a well-formed type` };
      requireRule(s1.tag, s2.tag, rules, `abstraction λ${t.param}:${show(t.annot)}. …`);
      return Pi(t.param, t.annot, tb);
    }
    case 'pi': {
      const s1 = infer(ctx, t.annot, env, rules);
      if (!isSort(s1)) throw { message: `domain ${show(t.annot)} must be a type, but it has type ${show(s1)}` };
      const ctx2 = [...ctx, { name: t.param, type: t.annot }];
      const s2 = infer(ctx2, t.body, env, rules);
      if (!isSort(s2)) throw { message: `codomain ${show(t.body)} must be a type` };
      requireRule(s1.tag, s2.tag, rules, `Π-type Π(${dispName(t.param)}:${show(t.annot)}). …`);
      return s2.tag === 'star' ? Star() : Box();
    }
  }
}

// ---------- programs ----------
function buildEnv(prog) {
  const env = {};
  for (const d of prog.defs) {
    env[d.name] = d.kind === 'axiom'
      ? { type: d.type, value: null }
      : { type: d.annot, value: d.value };
  }
  return env;
}

// Parse without typechecking (for the evaluator, untyped mode included).
function evalProgram(src) {
  const prog = parse(src);
  return { prog, env: buildEnv(prog), final: prog.final };
}

// Full check: typecheck every definition in order, then the final expression.
// rules: {poly, typeops, dep}. Returns {lines, finalType, env, prog}.
function checkProgram(src, rules) {
  const prog = parse(src);
  const env = {};
  const lines = [];
  for (const d of prog.defs) {
    if (env[d.name]) throw { message: `'${d.name}' is already defined` };
    if (d.kind === 'axiom') {
      const s = infer([], d.type, env, rules);
      if (!isSort(s)) throw { message: `axiom ${d.name}: ${show(d.type)} is not a type` };
      env[d.name] = { type: d.type, value: null };
      lines.push(`${d.name} : ${show(d.type)}    (axiom)`);
    } else if (d.annot) {
      const s = infer([], d.annot, env, rules);
      if (!isSort(s)) throw { message: `${d.name}: declared type ${show(d.annot)} is not a well-formed type` };
      const tv = infer([], d.value, env, rules);
      if (!conv(tv, d.annot, env)) {
        throw { message: `${d.name}: declared type does not match inferred type\n  declared: ${show(d.annot)}\n  inferred: ${show(tv)}` };
      }
      env[d.name] = { type: d.annot, value: d.value };
      lines.push(`${d.name} : ${show(d.annot)}`);
    } else {
      const tv = infer([], d.value, env, rules);
      env[d.name] = { type: tv, value: d.value };
      lines.push(`${d.name} : ${show(tv)}`);
    }
  }
  let finalType = null;
  if (prog.final) finalType = infer([], prog.final, env, rules);
  return { lines, finalType, env, prog };
}

const LambdaCore = {
  Star, Box, Var, App, Lam, Pi,
  tokenize, parse, freeVars, subst,
  step, normalize, whnf, alphaEq, conv, show, infer,
  evalProgram, checkProgram,
};
if (typeof module !== 'undefined') module.exports = LambdaCore;
if (typeof window !== 'undefined') window.LambdaCore = LambdaCore;
})();
