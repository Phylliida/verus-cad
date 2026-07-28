/* examples.js — gallery for the playground. `mode` selects the engine:
 * 'pts' (lambda cube checker), 'bckw' (combinators), 'cek' (environment machine).
 * For pts examples, poly/typeops/dep set the cube axes. */
const EXAMPLES = [
  // ---------- λ-cube mode ----------
  {
    name: 'untyped: Church numerals, add 2 3',
    mode: 'pts', poly: false, typeops: false, dep: false,
    src: `// untyped lambda calculus — no annotations, evaluation only
two   := λf. λx. f (f x);
three := λf. λx. f (f (f x));
add   := λm. λn. λf. λx. m f (n f x);
add two three   // hit "normalize" — you should get five`,
  },
  {
    name: 'untyped: Ω diverges',
    mode: 'pts', poly: false, typeops: false, dep: false,
    src: `// the classic looping term — "normalize" gives up after 1000 steps,
// "step" lets you watch it spin forever
(λx. x x) (λx. x x)`,
  },
  {
    name: 'λ→: identity on Bool',
    mode: 'pts', poly: false, typeops: false, dep: false,
    src: `// simply typed lambda calculus — the base of the cube, rule (⋆,⋆) only
axiom Bool : ⋆;
axiom true : Bool;
id := λb:Bool. b;
id true`,
  },
  {
    name: 'λ2: polymorphic identity',
    mode: 'pts', poly: true, typeops: false, dep: false,
    src: `// System F — a term abstracted over a type, rule (□,⋆)
// (load me, then turn polymorphism OFF and re-check to see it fail)
axiom Bool : ⋆;
axiom true : Bool;
id : Π(A:⋆). A → A := λA:⋆. λx:A. x;
id Bool true`,
  },
  {
    name: 'λω̲: a type operator',
    mode: 'pts', poly: false, typeops: true, dep: false,
    src: `// types depending on types, rule (□,□)
// Dup is a function *on types* — reduce it with "normalize" too
axiom Nat : ⋆;
Dup : ⋆ → ⋆ := λA:⋆. A → A;
f : Dup Nat := λn:Nat. n;   // Dup Nat ≡ Nat → Nat by beta-reduction on types
f`,
  },
  {
    name: 'λP: vectors indexed by Nat',
    mode: 'pts', poly: false, typeops: false, dep: true,
    src: `// types depending on terms, rule (⋆,□)
// Vec n is a type *family* — the type depends on the value n
axiom Nat : ⋆;
axiom zero : Nat;
axiom Vec : Nat → ⋆;
axiom nil : Vec zero;
headInto := λn:Nat. λv:(Vec n). v;
headInto zero nil`,
  },
  {
    name: 'λC: Leibniz equality',
    mode: 'pts', poly: true, typeops: true, dep: true,
    src: `// Calculus of Constructions — the whole cube.
// "x equals y iff every property of x is a property of y", from nothing.
axiom Nat : ⋆;
axiom zero : Nat;
Eq : Π(A:⋆). A → A → ⋆ :=
  λA:⋆. λx:A. λy:A. Π(P:(A → ⋆)). P x → P y;
refl : Π(A:⋆). Π(x:A). Eq A x x :=
  λA:⋆. λx:A. λP:(A → ⋆). λpx:(P x). px;
refl Nat zero   // a proof that zero = zero, as an object you built`,
  },

  // ---------- combinator mode ----------
  {
    name: 'BCKW: the combinators introduce themselves',
    mode: 'bckw',
    src: `// compile + infer: watch each lambda become a combinator with its
// principal type — these types ARE theorems of propositional logic
compose := λf. λg. λx. f (g x);
const   := λx. λy. x;
flip    := λf. λx. λy. f y x;
dup     := λf. λx. f x x;
compose`,
  },
  {
    name: 'BCKW: Church numerals stay compact',
    mode: 'bckw',
    src: `// same program as the λ-mode example, compiled to combinators.
// defs are compiled ONCE and referenced by name — compare the node counts.
// then "normalize": s and z are free constants, so the numeral reads off
two   := λf. λx. f (f x);
three := λf. λx. f (f (f x));
add   := λm. λn. λf. λx. m f (n f x);
add two three s z`,
  },
  {
    name: 'BCKW: S K K = I, and self-application is untypable',
    mode: 'bckw',
    src: `// "compile + infer" shows skk : a → a, same as I — try normalizing
// (S K K z) to watch it compute to z in tiny local steps.
// then delete the z and change the last line to:  λx. x x
// and re-compile — the occurs check rejects it: no infinite types allowed
skk := S K K;
skk z`,
  },
  {
    name: 'CEK: add 2 3 on the environment machine',
    mode: 'cek',
    src: `// same Church numerals, but "step" now shows a machine state:
// control / env / kont — closures and lookups, zero substitution.
// "run" evaluates to a closure; compare the trace with λ-mode's.
two   := λf. λx. f (f x);
three := λf. λx. f (f (f x));
add   := λm. λn. λf. λx. m f (n f x);
add two three`,
  },
];
if (typeof module !== 'undefined') module.exports = EXAMPLES;
