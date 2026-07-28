/* test.js — run with: node test.js */
'use strict';
const L = require('./lambda.js');
const CB = require('./combinators.js');
const MK = require('./machine.js');
const EXAMPLES = require('./examples.js');

let pass = 0, fail = 0;
function ok(cond, msg) {
  if (cond) { pass++; console.log('ok   - ' + msg); }
  else { fail++; console.log('FAIL - ' + msg); }
}
function throwsWith(fn, substr, msg) {
  try { fn(); fail++; console.log('FAIL - ' + msg + ' (did not throw)'); }
  catch (e) {
    const m = e.message || String(e);
    ok(m.includes(substr), msg + (m.includes(substr) ? '' : ` (wrong error: ${m.split('\n')[0]})`));
  }
}

const ALL = { poly: true, typeops: true, dep: true };
const NONE = { poly: false, typeops: false, dep: false };
const only = k => ({ ...NONE, [k]: true });

// 1. Church numerals: add 2 3 normalizes to 5
{
  const p = L.evalProgram(EXAMPLES[0].src);
  const r = L.normalize(p.final, p.env, 1000);
  const five = L.parse('λf. λx. f (f (f (f (f x))))').final;
  ok(!r.capped && r.steps > 0, `church: add two three terminates (${r.steps} steps)`);
  ok(L.alphaEq(r.term, five), 'church: add two three ≡ λf. λx. f⁵x (up to alpha)');
}

// 2. Omega diverges
{
  const p = L.evalProgram(EXAMPLES[1].src);
  const r = L.normalize(p.final, p.env, 200);
  ok(r.capped, 'omega: (λx. x x)(λx. x x) does not terminate within cap');
}

// 3–7. Typed pts examples check with their required toggles, expected final types
const expectedTypes = ['Bool', 'Bool', 'Dup Nat', 'Vec zero', 'Eq Nat zero zero'];
EXAMPLES.slice(2, 7).forEach((ex, i) => {
  const rules = { poly: ex.poly, typeops: ex.typeops, dep: ex.dep };
  try {
    const r = L.checkProgram(ex.src, rules);
    ok(L.show(r.finalType) === expectedTypes[i],
      `${ex.name}: checks, type ${L.show(r.finalType)}`);
  } catch (e) {
    fail++; console.log(`FAIL - ${ex.name}: threw: ${(e.message || e).split('\n')[0]}`);
  }
});

// 8. polymorphic id needs the polymorphism axis
throwsWith(() => L.checkProgram(EXAMPLES[3].src, NONE), 'polymorphism',
  'λ2 example fails with all toggles off, error mentions polymorphism');

// 9. vectors need the dependent-types axis
throwsWith(() => L.checkProgram(EXAMPLES[5].src, NONE), 'dependent',
  'λP example fails with all toggles off, error mentions dependent types');

// 10. type operators need their axis too
throwsWith(() => L.checkProgram(EXAMPLES[4].src, NONE), 'type operators',
  'λω̲ example fails with all toggles off, error mentions type operators');

// 11. beta through type application: id Bool true evaluates to true
{
  const p = L.evalProgram(EXAMPLES[3].src);
  const r = L.normalize(p.final, p.env, 1000);
  ok(!r.capped && L.show(r.term) === 'true', 'eval: id Bool true ⟶* true');
}

// 12. alpha equivalence of Π-types with different binder names
{
  const a = L.parse('Π(A:⋆). A → A').final;
  const b = L.parse('Π(B:⋆). B → B').final;
  ok(L.conv(a, b, {}), 'alpha: Π(A:⋆). A→A  ≡  Π(B:⋆). B→B');
}

// 13. untyped programs are rejected by the checker with the untyped code
throwsWith(() => L.checkProgram(EXAMPLES[0].src, NONE), 'untyped',
  'untyped program reported as untyped (evaluation-only mode)');

// 14. capture avoidance: (λx. λy. x) y  ⟶*  λy₁. y  (not λy. y)
{
  const t = L.parse('(λx. λy. x) y').final;
  const r = L.normalize(t, {}, 100);
  const nf = r.term;
  ok(nf.tag === 'lam' && /^y#\d+$/.test(nf.param) && nf.body.tag === 'var' && nf.body.name === 'y',
    `capture: (λx. λy. x) y ⟶* ${L.show(nf)} (binder freshened, no capture)`);
}

// ---------- combinators (BCKW mode) ----------
const csrc = s => L.parse(s).final;

// 15. Turner compilation: exact compact combinator forms
ok(L.show(CB.compile(csrc('λx. x'))) === 'I', 'compile: λx. x ↦ I');
ok(L.show(CB.compile(csrc('λx. λy. x'))) === 'K', 'compile: λx. λy. x ↦ K');
ok(L.show(CB.compile(csrc('λf. λg. λx. f (g x)'))) === 'B', 'compile: compose ↦ B');
ok(L.show(CB.compile(csrc('λf. λx. f (f x)'))) === 'S B I', 'compile: church two ↦ S B I (compact)');
ok(L.show(CB.compile(csrc('λf. λx. f x x'))) === 'C S I', 'compile: dup ↦ C S I');

// 16. combinator reduction is local and correct: S K K z ⟶* z
{
  const r = CB.normalizeComb(csrc('S K K z'), {}, 100);
  ok(!r.capped && L.show(r.term) === 'z', `reduce: S K K z ⟶* z (${r.steps} steps)`);
}

// 17. BCKW Church example: add two three s z ⟶* s⁵z (defs shared, not inlined)
{
  const ex = EXAMPLES.find(e => e.name.includes('stay compact'));
  const r = CB.compileProgram(ex.src);
  const n = CB.normalizeComb(r.finalCompiled, r.env, 1000);
  ok(!n.capped && L.show(n.term) === 's (s (s (s (s z))))',
    `bckw church: add two three s z ⟶* s⁵z (${n.steps} steps)`);
  ok(r.lamSize > 0 && r.combSize > 0, `bckw church: size report ${r.lamSize} → ${r.combSize} nodes`);
}

// 18. principal types come out as Hilbert axioms
{
  const ty = src => CB.showType(CB.compileProgram(src).finalType, CB.compileProgram(src).sub);
  ok(ty('id := λx. x; id') === 'a → a', 'infer: id : a → a');
  ok(ty('const := λx. λy. x; const') === 'a → b → a', 'infer: const : a → b → a  (= K axiom)');
  ok(ty('skk := S K K; skk') === 'a → a', 'infer: S K K : a → a  (= I)');
  ok(ty('dup := λf. λx. f x x; dup') === '(a → a → b) → a → b', 'infer: dup : (a → a → b) → a → b  (= W axiom)');
  ok(ty('compose := λf. λg. λx. f (g x); compose') === '(a → b) → (c → a) → c → b', 'infer: compose : (a → b) → (c → a) → c → b  (= B axiom)');
}

// 19. self-application is rejected by the occurs check
throwsWith(() => CB.compileProgram('λx. x x'), 'occurs check',
  'infer: λx. x x is untypable (occurs check)');

// ---------- CEK machine ----------
// 20. CEK evaluates with closures, no substitution
{
  const st = MK.cekRun(MK.cekInit('(λx. x) (λy. y)'), 100);
  ok(st.done && st.control.tag === 'closure' && L.show(st.control.lam) === 'λy. y',
    `cek: (λx. x)(λy. y) ⇓ closure «λy. y» (${st.steps} machine steps)`);
}

// 21. CEK runs the Church example to a closure value
{
  const ex = EXAMPLES.find(e => e.mode === 'cek');
  const st = MK.cekRun(MK.cekInit(ex.src), 1000);
  ok(st.done && st.control.tag === 'closure', `cek church: add two three ⇓ closure (${st.steps} machine steps)`);
}

// 22. CEK free variable gets stuck with a clear message
{
  const st = MK.cekRun(MK.cekInit('x'), 100);
  ok(st.stuck && st.stuck.includes("no value for 'x'"), 'cek: free variable reports stuck, not a crash');
}

console.log(`\n${pass} passed, ${fail} failed`);
process.exit(fail ? 1 : 0);
