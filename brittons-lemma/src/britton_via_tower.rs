//  Britton's Lemma via Tower Construction
//
//  Translates HNN extension derivations to tower derivations.
//  Faithful to Lyndon-Schupp Chapter IV: the tower unfolds the HNN extension
//  by replacing the stable letter with explicit copies of the base group.
//
//  Key insight: the HNN relator t⁻¹·a_i·t·inv(b_i) at level k corresponds
//  exactly to the AFP identification relator shift(a_i, (k-1)·ng)·inv(shift(b_i, k·ng))
//  at tower junction (k-1)↔k.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::reduction::*;
use crate::benign::*;
use crate::hnn::*;
use crate::tower::*;

verus! {

///  The HNN presentation is a valid presentation.
///  (Inlined from britton_proof.rs to avoid pulling in the 14k-line file.)
proof fn lemma_hnn_presentation_valid(data: HNNData)
    requires
        hnn_data_valid(data),
    ensures
        presentation_valid(hnn_presentation(data)),
{
    reveal(presentation_valid);
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    assert forall|i: int| #![trigger hp.relators[i]]
        0 <= i < hp.relators.len()
        implies word_valid(hp.relators[i], hp.num_generators)
    by {
        let base_len = data.base.relators.len() as int;
        if i < base_len {
            assert(hp.relators[i] == data.base.relators[i]);
            assert(word_valid(data.base.relators[i], n));
            assert forall|j: int| 0 <= j < hp.relators[i].len()
                implies symbol_valid(#[trigger] hp.relators[i][j], hp.num_generators)
            by {
                assert(symbol_valid(hp.relators[i][j], n));
                match hp.relators[i][j] {
                    Symbol::Gen(idx) => {}
                    Symbol::Inv(idx) => {}
                }
            }
        } else {
            let k = (i - base_len);
            let (a_k, b_k) = data.associations[k];
            assert(word_valid(a_k, n));
            assert(word_valid(b_k, n));
            lemma_inverse_word_valid(b_k, n);
            let r = hp.relators[i];
            assert forall|j: int| 0 <= j < r.len()
                implies symbol_valid(#[trigger] r[j], n + 1)
            by {
                if j == 0 {
                } else if (j as int) < 1 + a_k.len() {
                    let aj = (j - 1) as int;
                    assert(symbol_valid(a_k[aj], n));
                    match a_k[aj] { Symbol::Gen(idx) => {} Symbol::Inv(idx) => {} }
                } else if j == 1 + a_k.len() {
                } else {
                    let inv_bk = inverse_word(b_k);
                    let bj = (j - 2 - a_k.len()) as int;
                    assert(symbol_valid(inv_bk[bj], n));
                    match inv_bk[bj] { Symbol::Gen(idx) => {} Symbol::Inv(idx) => {} }
                }
            }
        }
    }
}

//  ============================================================
//  Part A: Level tracking and word translation
//  ============================================================

///  Whether symbol s is the stable letter t or t⁻¹.
pub open spec fn is_stable(data: HNNData, s: Symbol) -> bool {
    let ng = data.base.num_generators;
    s == Symbol::Gen(ng) || s == Symbol::Inv(ng)
}

///  Net level change of a word: count of t minus count of t⁻¹.
pub open spec fn net_level(data: HNNData, w: Word) -> int
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
        0
    } else {
        let s = w.first();
        let rest_level = net_level(data, w.drop_first());
        if s == Symbol::Gen(ng) {
            1 + rest_level
        } else if s == Symbol::Inv(ng) {
            -1 + rest_level
        } else {
            rest_level
        }
    }
}

///  Translate an HNN word to a tower word, starting at a given base level.
///  - Stable letters are REMOVED (encode level changes)
///  - Base symbol at current level k becomes shifted by k·ng
///  - base_level tracks the accumulated level from earlier context
pub open spec fn translate_word_at(data: HNNData, w: Word, base_level: int) -> Word
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
        empty_word()
    } else {
        let s = w.first();
        let rest = w.drop_first();
        if s == Symbol::Gen(ng) {
            //  t: level +1, skip symbol
            translate_word_at(data, rest, base_level + 1)
        } else if s == Symbol::Inv(ng) {
            //  t⁻¹: level -1, skip symbol
            translate_word_at(data, rest, base_level - 1)
        } else {
            //  Base symbol: shift by base_level · ng, include in output
            let shifted_s = match s {
                Symbol::Gen(i) => Symbol::Gen((i + base_level * ng) as nat),
                Symbol::Inv(i) => Symbol::Inv((i + base_level * ng) as nat),
            };
            concat(Seq::new(1, |_j: int| shifted_s),
                translate_word_at(data, rest, base_level))
        }
    }
}

///  Top-level translation: start at level 0.
pub open spec fn translate_word(data: HNNData, w: Word) -> Word {
    translate_word_at(data, w, 0)
}

//  ============================================================
//  Part B: Base word translation = identity
//  ============================================================

///  A base word has net level 0.
proof fn lemma_base_word_net_level_zero(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        net_level(data, w) == 0,
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
        lemma_base_word_net_level_zero(data, w.drop_first());
    }
}

///  A base word translates to itself at level 0.
pub proof fn lemma_translate_base_word(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        translate_word(data, w) =~= w,
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); assert(!is_stable(data, s)); }
            Symbol::Inv(i) => { assert(i < ng); assert(!is_stable(data, s)); }
        }
        assert(word_valid(w.drop_first(), ng));
        lemma_translate_base_word(data, w.drop_first());
    }
}

///  The empty word translates to the empty word.
pub proof fn lemma_translate_empty(data: HNNData)
    ensures translate_word(data, empty_word()) =~= empty_word(),
{
}

//  ============================================================
//  Part C: Concat decomposition for translate_word_at
//  ============================================================

///  translate_word_at distributes over concat (with level offset).
pub proof fn lemma_translate_concat(data: HNNData, w1: Word, w2: Word, base_level: int)
    ensures
        translate_word_at(data, concat(w1, w2), base_level)
            =~= concat(translate_word_at(data, w1, base_level),
                        translate_word_at(data, w2, base_level + net_level(data, w1))),
    decreases w1.len(),
{
    let ng = data.base.num_generators;
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(net_level(data, w1) == 0);
        assert(translate_word_at(data, w1, base_level) =~= empty_word());
    } else {
        let s = w1.first();
        let rest1 = w1.drop_first();
        assert(concat(w1, w2).first() == s);
        assert(concat(w1, w2).drop_first() =~= concat(rest1, w2));

        if s == Symbol::Gen(ng) {
            lemma_translate_concat(data, rest1, w2, base_level + 1);
        } else if s == Symbol::Inv(ng) {
            lemma_translate_concat(data, rest1, w2, base_level - 1);
        } else {
            lemma_translate_concat(data, rest1, w2, base_level);
        }
    }
}

//  ============================================================
//  Part D: Derivation lifting — equiv in p1 → equiv in free_product(p1, p2)
//  ============================================================

///  A single derivation step valid in p1 is also valid in free_product(p1, p2).
proof fn lemma_step_valid_in_fp_left(
    p1: Presentation, p2: Presentation,
    w: Word, step: DerivationStep,
)
    requires
        apply_step(p1, w, step) is Some,
    ensures
        apply_step(free_product(p1, p2), w, step) == apply_step(p1, w, step),
{
    let fp = free_product(p1, p2);
    match step {
        DerivationStep::FreeReduce { position } => {},
        DerivationStep::FreeExpand { position, symbol } => {
            assert(symbol_valid(symbol, fp.num_generators)) by {
                match symbol {
                    Symbol::Gen(i) => {}
                    Symbol::Inv(i) => {}
                }
            }
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
        },
    }
}

///  A full derivation valid in p1 is also valid in free_product(p1, p2).
proof fn lemma_derivation_valid_in_fp_left(
    p1: Presentation, p2: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(p1, steps, w1) == Some(w2),
    ensures
        derivation_produces(free_product(p1, p2), steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let w_mid = apply_step(p1, w1, steps.first()).unwrap();
        lemma_step_valid_in_fp_left(p1, p2, w1, steps.first());
        lemma_derivation_valid_in_fp_left(p1, p2, steps.drop_first(), w_mid, w2);
    }
}

///  Equivalence in p1 implies equivalence in free_product(p1, p2).
pub proof fn lemma_left_embeds_in_fp(
    p1: Presentation, p2: Presentation, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(p1, w1, w2),
    ensures
        equiv_in_presentation(free_product(p1, p2), w1, w2),
{
    let d: Derivation = choose|d: Derivation| derivation_valid(p1, d, w1, w2);
    lemma_derivation_valid_in_fp_left(p1, p2, d.steps, w1, w2);
    let d_fp = Derivation { steps: d.steps };
    assert(derivation_valid(free_product(p1, p2), d_fp, w1, w2));
}

///  Equivalence in tower(k) implies equivalence in tower(m) for k ≤ m.
pub proof fn lemma_tower_monotone(
    data: HNNData, k: nat, m: nat, w1: Word, w2: Word,
)
    requires
        hnn_data_valid(data),
        k <= m,
        equiv_in_presentation(tower_presentation(data, k), w1, w2),
    ensures
        equiv_in_presentation(tower_presentation(data, m), w1, w2),
    decreases m - k,
{
    if k == m {
    } else {
        let afp_data = tower_afp_data(data, k);
        lemma_left_embeds_in_fp(afp_data.p1, afp_data.p2, w1, w2);
        crate::quotient::lemma_add_relators_preserves_equiv(
            free_product(afp_data.p1, afp_data.p2),
            amalgamation_relators(afp_data), w1, w2);
        lemma_tower_monotone(data, k + 1, m, w1, w2);
    }
}

//  ============================================================
//  Part E: Tower relator correspondence
//  ============================================================

///  A base relator at copy k is equiv to ε in tower(m) when k ≤ m.
pub proof fn lemma_base_relator_in_tower(
    data: HNNData, m: nat, k: nat, r: int,
)
    requires
        hnn_data_valid(data),
        k <= m,
        0 <= r < data.base.relators.len(),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            shift_word(data.base.relators[r], k * data.base.num_generators),
            empty_word()),
    decreases m,
{
    let ng = data.base.num_generators;
    if k == 0 && m == 0 {
        assert(shift_word(data.base.relators[r], 0) =~= data.base.relators[r]);
        lemma_relator_is_identity(data.base, r);
    } else if k < m {
        if k == 0 {
            assert(shift_word(data.base.relators[r], 0) =~= data.base.relators[r]);
            lemma_relator_is_identity(data.base, r);
            lemma_tower_monotone(data, 0, m, data.base.relators[r], empty_word());
        } else {
            lemma_base_relator_in_tower(data, (m - 1) as nat, k, r);
            lemma_tower_monotone(data, (m - 1) as nat, m,
                shift_word(data.base.relators[r], k * ng), empty_word());
        }
    } else {
        //  k == m > 0: relator in the new copy (right factor)
        let prev = (m - 1) as nat;
        let afp_data = tower_afp_data(data, prev);
        let fp = free_product(afp_data.p1, afp_data.p2);
        lemma_tower_num_generators(data, prev);
        let fp_idx = (afp_data.p1.relators.len() + r) as nat;
        assert(fp.relators[fp_idx as int]
            == shift_word(data.base.relators[r], m * ng));
        lemma_relator_is_identity(fp, fp_idx as int);
        crate::quotient::lemma_add_relators_preserves_equiv(
            fp, amalgamation_relators(afp_data),
            shift_word(data.base.relators[r], m * ng), empty_word());
    }
}

///  An identification relator at junction k↔k+1 is equiv to ε in tower(m) when k+1 ≤ m.
pub proof fn lemma_ident_relator_in_tower(
    data: HNNData, m: nat, k: nat, i: int,
)
    requires
        hnn_data_valid(data),
        k + 1 <= m,
        0 <= i < data.associations.len() as int,
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            amalgamation_relator(tower_afp_data(data, k), i),
            empty_word()),
    decreases m,
{
    let prev = (m - 1) as nat;
    let afp_data = tower_afp_data(data, prev);
    let fp = free_product(afp_data.p1, afp_data.p2);

    if k == prev {
        crate::quotient::lemma_each_added_relator_is_identity(
            fp, amalgamation_relators(afp_data), i);
    } else {
        lemma_ident_relator_in_tower(data, prev, k, i);
        lemma_tower_monotone(data, prev, m,
            amalgamation_relator(tower_afp_data(data, k), i), empty_word());
    }
}

//  ============================================================
//  Part F: Context insertion — if r ≡ ε, then prefix·suffix ≡ prefix·r·suffix
//  ============================================================

///  If r ≡ ε, then prefix·r·suffix ≡ prefix·suffix (deletion direction).
pub proof fn lemma_delete_equiv_empty(
    p: Presentation, prefix: Word, r: Word, suffix: Word,
)
    requires
        equiv_in_presentation(p, r, empty_word()),
    ensures
        equiv_in_presentation(p, concat(prefix, concat(r, suffix)),
            concat(prefix, suffix)),
{
    //  r ≡ ε → concat(r, suffix) ≡ concat(ε, suffix) =~= suffix
    lemma_equiv_concat_left(p, r, empty_word(), suffix);
    //  concat(prefix, concat(r, suffix)) ≡ concat(prefix, suffix)
    lemma_equiv_concat_right(p, prefix, concat(r, suffix), suffix);
}

///  If r ≡ ε, then prefix·suffix ≡ prefix·r·suffix (insertion direction).
///  Requires symmetry infrastructure (word_valid + presentation_valid).
pub proof fn lemma_insert_equiv_empty(
    p: Presentation, prefix: Word, r: Word, suffix: Word,
)
    requires
        equiv_in_presentation(p, r, empty_word()),
        presentation_valid(p),
        word_valid(r, p.num_generators),
    ensures
        equiv_in_presentation(p, concat(prefix, suffix),
            concat(prefix, concat(r, suffix))),
{
    //  ε ≡ r (by symmetry)
    crate::presentation::lemma_equiv_symmetric(p, r, empty_word());
    //  concat(ε, suffix) ≡ concat(r, suffix) → suffix ≡ concat(r, suffix)
    lemma_equiv_concat_left(p, empty_word(), r, suffix);
    //  concat(prefix, suffix) ≡ concat(prefix, concat(r, suffix))
    lemma_equiv_concat_right(p, prefix, suffix, concat(r, suffix));
}

//  ============================================================
//  Part G: Translation of base words at arbitrary level
//  ============================================================

///  A base word at level L translates to shift_word(w, L * ng).
pub proof fn lemma_translate_base_word_at(data: HNNData, w: Word, base_level: nat)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        translate_word_at(data, w, base_level as int)
            =~= shift_word(w, base_level * data.base.num_generators),
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
        lemma_translate_base_word_at(data, w.drop_first(), base_level);
    }
}

///  A single stable letter translates to empty at any level.
proof fn lemma_translate_stable_empty(data: HNNData, s: Symbol, base_level: int)
    requires is_stable(data, s),
    ensures
        translate_word_at(data, Seq::new(1, |_j: int| s), base_level) =~= empty_word(),
{
    let w = Seq::new(1, |_j: int| s);
    assert(w.first() == s);
    assert(w.drop_first() =~= Seq::<Symbol>::empty());
    reveal_with_fuel(translate_word_at, 2);
}

///  Net level of a base word is 0.
proof fn lemma_net_level_base_word(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        net_level(data, w) == 0,
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
        lemma_net_level_base_word(data, w.drop_first());
    }
}

///  Net level of a single stable letter.
proof fn lemma_net_level_stable(data: HNNData, s: Symbol)
    requires is_stable(data, s),
    ensures
        net_level(data, Seq::new(1, |_j: int| s)) ==
            (if s == Symbol::Gen(data.base.num_generators) { 1int } else { -1int }),
{
    let w = Seq::new(1, |_j: int| s);
    assert(w.first() == s);
    assert(w.drop_first() =~= Seq::<Symbol>::empty());
    reveal_with_fuel(net_level, 2);
}

///  Net level distributes over concat.
pub proof fn lemma_net_level_concat(data: HNNData, w1: Word, w2: Word)
    ensures
        net_level(data, concat(w1, w2)) == net_level(data, w1) + net_level(data, w2),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
    } else {
        assert(concat(w1, w2).first() == w1.first());
        assert(concat(w1, w2).drop_first() =~= concat(w1.drop_first(), w2));
        lemma_net_level_concat(data, w1.drop_first(), w2);
    }
}

//  ============================================================
//  Part H: HNN relator translates to identification relator
//  ============================================================

///  The HNN relator t⁻¹·a_i·t·inv(b_i) at level k translates to
///  the AFP identification relator at junction (k-1)↔k.
///
///  This is the textbook correspondence (Lyndon-Schupp Ch. IV):
///  each HNN relation at level k becomes an identification relation
///  between copy k-1 and copy k in the tower.
pub proof fn lemma_translate_hnn_relator(
    data: HNNData, i: int, k: int,
)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
        k >= 1,
    ensures ({
        let ng = data.base.num_generators;
        let r = hnn_relator(data, i);
        let afp_data = tower_afp_data(data, (k - 1) as nat);
        translate_word_at(data, r, k)
            =~= amalgamation_relator(afp_data, i)
    }),
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    let t_inv = Seq::new(1, |_j: int| Symbol::Inv(ng));
    let t_gen = Seq::new(1, |_j: int| Symbol::Gen(ng));

    //  r = concat(part1, part2) where part1 = concat(t_inv, a_i), part2 = concat(t_gen, inv(b_i))
    let part1 = concat(t_inv, a_i);
    let part2 = concat(t_gen, inverse_word(b_i));

    //  Step 1: decompose r = concat(part1, part2)
    lemma_translate_concat(data, part1, part2, k);

    //  Step 2: net_level(part1) = -1 (t⁻¹ contributes -1, a_i contributes 0)
    lemma_net_level_concat(data, t_inv, a_i);
    lemma_net_level_stable(data, Symbol::Inv(ng));
    lemma_net_level_base_word(data, a_i);
    assert(net_level(data, part1) == -1);

    //  Step 3: translate(part1, k) =~= shift(a_i, (k-1)*ng)
    lemma_translate_concat(data, t_inv, a_i, k);
    lemma_net_level_stable(data, Symbol::Inv(ng));
    lemma_translate_stable_empty(data, Symbol::Inv(ng), k);
    lemma_translate_base_word_at(data, a_i, (k - 1) as nat);

    //  Step 4: translate(part2, k-1) =~= shift(inv(b_i), k*ng)
    lemma_translate_concat(data, t_gen, inverse_word(b_i), k - 1);
    lemma_net_level_stable(data, Symbol::Gen(ng));
    lemma_translate_stable_empty(data, Symbol::Gen(ng), k - 1);
    crate::word::lemma_inverse_word_valid(b_i, ng);
    lemma_translate_base_word_at(data, inverse_word(b_i), k as nat);

    //  Intermediate assertions to chain the =~= results
    assert(translate_word_at(data, part1, k)
        =~= shift_word(a_i, ((k - 1) as nat) * ng));
    assert(translate_word_at(data, part2, k - 1)
        =~= shift_word(inverse_word(b_i), k as nat * ng));

    //  Step 5: shift(inv(b_i), k*ng) =~= inv(shift(b_i, k*ng))
    crate::free_product::lemma_shift_inverse_word(b_i, k as nat * ng);

    //  Step 6: connect to amalgamation_relator
    lemma_tower_num_generators(data, (k - 1) as nat);
    assert(translate_word_at(data, part2, k - 1)
        =~= inverse_word(shift_word(b_i, k as nat * ng)));

    //  Connect hnn_relator to concat(part1, part2)
    assert(hnn_relator(data, i) =~= concat(part1, part2));

    //  Final chain
    assert(translate_word_at(data, concat(part1, part2), k)
        =~= concat(shift_word(a_i, ((k - 1) as nat) * ng),
                    inverse_word(shift_word(b_i, k as nat * ng))));
}

//  ============================================================
//  Part I: General middle-deletion lemma for translation
//  ============================================================

///  If the translated middle ≡ ε in tower and net_level(middle) == 0,
///  then translate(prefix · middle · suffix) ≡ translate(prefix · suffix) in tower.
///
///  This handles ALL step types uniformly:
///  - FreeReduce/Delete: w = prefix · middle · suffix → w' = prefix · suffix
///  - FreeExpand/Insert: w = prefix · suffix → w' = prefix · middle · suffix (reverse direction)
pub proof fn lemma_translate_delete_middle(
    data: HNNData, m: nat, base_level: int,
    prefix: Word, middle: Word, suffix: Word,
)
    requires
        hnn_data_valid(data),
        net_level(data, middle) == 0,
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, middle, base_level + net_level(data, prefix)),
            empty_word()),
        presentation_valid(tower_presentation(data, m)),
        word_valid(translate_word_at(data, middle, base_level + net_level(data, prefix)),
            tower_presentation(data, m).num_generators),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, concat(prefix, concat(middle, suffix)), base_level),
            translate_word_at(data, concat(prefix, suffix), base_level)),
{
    let tp = tower_presentation(data, m);
    let lp = base_level + net_level(data, prefix);

    //  Decompose translate of w = prefix · middle · suffix
    lemma_translate_concat(data, prefix, concat(middle, suffix), base_level);
    lemma_translate_concat(data, middle, suffix, lp);
    lemma_net_level_concat(data, prefix, concat(middle, suffix));
    lemma_net_level_concat(data, middle, suffix);

    //  Decompose translate of w' = prefix · suffix
    lemma_translate_concat(data, prefix, suffix, base_level);

    let tr_prefix = translate_word_at(data, prefix, base_level);
    let tr_middle = translate_word_at(data, middle, lp);
    let tr_suffix = translate_word_at(data, suffix, lp);

    lemma_delete_equiv_empty(tp, tr_prefix, tr_middle, tr_suffix);
}

///  Reverse direction: translate(prefix · suffix) ≡ translate(prefix · middle · suffix).
///  Needs symmetry infrastructure.
pub proof fn lemma_translate_insert_middle(
    data: HNNData, m: nat, base_level: int,
    prefix: Word, middle: Word, suffix: Word,
)
    requires
        hnn_data_valid(data),
        net_level(data, middle) == 0,
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, middle, base_level + net_level(data, prefix)),
            empty_word()),
        presentation_valid(tower_presentation(data, m)),
        word_valid(translate_word_at(data, middle, base_level + net_level(data, prefix)),
            tower_presentation(data, m).num_generators),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, concat(prefix, suffix), base_level),
            translate_word_at(data, concat(prefix, concat(middle, suffix)), base_level)),
{
    let tp = tower_presentation(data, m);
    let lp = base_level + net_level(data, prefix);

    lemma_translate_concat(data, prefix, concat(middle, suffix), base_level);
    lemma_translate_concat(data, middle, suffix, lp);
    lemma_net_level_concat(data, prefix, concat(middle, suffix));
    lemma_net_level_concat(data, middle, suffix);
    lemma_translate_concat(data, prefix, suffix, base_level);

    let tr_prefix = translate_word_at(data, prefix, base_level);
    let tr_middle = translate_word_at(data, middle, lp);
    let tr_suffix = translate_word_at(data, suffix, lp);

    lemma_insert_equiv_empty(tp, tr_prefix, tr_middle, tr_suffix);
}

//  ============================================================
//  Part J: Specific middle ≡ ε results
//  ============================================================

///  A stable inverse pair translates to ε (=~=, not just ≡).
proof fn lemma_translate_stable_pair(data: HNNData, s: Symbol, base_level: int)
    requires
        is_stable(data, s),
    ensures
        translate_word_at(data,
            concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| inverse_symbol(s))),
            base_level)
            =~= empty_word(),
        net_level(data,
            concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| inverse_symbol(s))))
            == 0,
{
    let s_word = Seq::new(1, |_j: int| s);
    let inv_s_word = Seq::new(1, |_j: int| inverse_symbol(s));
    let pair = concat(s_word, inv_s_word);

    lemma_translate_concat(data, s_word, inv_s_word, base_level);
    lemma_net_level_concat(data, s_word, inv_s_word);
    lemma_net_level_stable(data, s);

    //  inverse_symbol of stable is also stable
    let ng = data.base.num_generators;
    assert(is_stable(data, inverse_symbol(s))) by {
        if s == Symbol::Gen(ng) {
            assert(inverse_symbol(s) == Symbol::Inv(ng));
        } else {
            assert(inverse_symbol(s) == Symbol::Gen(ng));
        }
    }
    lemma_translate_stable_empty(data, s, base_level);
    lemma_net_level_stable(data, inverse_symbol(s));

    if s == Symbol::Gen(ng) {
        lemma_translate_stable_empty(data, inverse_symbol(s), base_level + 1);
    } else {
        lemma_translate_stable_empty(data, inverse_symbol(s), base_level - 1);
    }
}

//  ============================================================
//  Part G2: Base at copy k embeds in tower via shift homomorphism
//  ============================================================

///  Shift homomorphism: base → tower(m), mapping Gen(i) → [Gen(i + k*ng)].
pub open spec fn shift_hom(data: HNNData, m: nat, k: nat) -> crate::homomorphism::HomomorphismData {
    let ng = data.base.num_generators;
    crate::homomorphism::HomomorphismData {
        source: data.base,
        target: tower_presentation(data, m),
        generator_images: Seq::new(ng, |i: int| Seq::new(1, |_j: int| Symbol::Gen((i + k * ng) as nat))),
    }
}

///  The shift homomorphism maps words to their shifted versions.
#[verifier::rlimit(200)]
proof fn lemma_shift_hom_applies(data: HNNData, k: nat, m: nat, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        crate::homomorphism::apply_hom(shift_hom(data, m, k), w)
            =~= shift_word(w, k * data.base.num_generators),
    decreases w.len(),
{
    let h = shift_hom(data, m, k);
    let ng = data.base.num_generators;
    let result = crate::homomorphism::apply_hom(h, w);
    let shifted = shift_word(w, k * ng);
    if w.len() == 0 {
        assert(result.len() == 0);
        assert(shifted.len() == 0);
    } else {
        lemma_shift_hom_applies(data, k, m, w.drop_first());
        //  IH: apply_hom(h, rest) =~= shift_word(rest, k*ng)
        //  result = concat(apply_hom_symbol(h, w.first()), apply_hom(h, rest))
        //  shifted = Seq::new(w.len(), |j| shift_symbol(w[j], k*ng))
        //  Element-wise: result[0] == shifted[0] and result[j] == shifted[j] for j > 0

        //  The result has same length as shifted
        let s = w.first();
        assert(symbol_valid(s, ng));
        let sym_img = crate::homomorphism::apply_hom_symbol(h, s);
        //  For both Gen and Inv: sym_img is a 1-element word = [shift_symbol(s, k*ng)]
        match s {
            Symbol::Gen(i) => {
                assert(sym_img.len() == 1);
                assert(sym_img[0] == shift_symbol(s, k * ng));
            }
            Symbol::Inv(i) => {
                //  sym_img = inverse_word([Gen(i+k*ng)]) = [Inv(i+k*ng)]
                let gen_img = h.generator_images[i as int];
                assert(gen_img.len() == 1);
                assert(gen_img[0] == Symbol::Gen((i + k * ng) as nat));
                //  inverse_word definition: Seq::new(w.len(), |j| inverse_symbol(w[w.len()-1-j]))
                //  For len=1: Seq::new(1, |j| inverse_symbol(gen_img[0])) = [Inv(i+k*ng)]
                crate::word::lemma_inverse_word_len(gen_img);
                assert(sym_img.len() == 1);
                assert(sym_img[0] == shift_symbol(s, k * ng));
            }
        }
    }
}

///  The shift homomorphism is valid: relator images ≡ ε in tower(m).
proof fn lemma_shift_hom_valid(data: HNNData, m: nat, k: nat)
    requires
        hnn_data_valid(data),
        k <= m,
    ensures
        crate::homomorphism::is_valid_homomorphism(shift_hom(data, m, k)),
{
    let h = shift_hom(data, m, k);
    let ng = data.base.num_generators;
    reveal(presentation_valid);
    lemma_tower_valid(data, m);
    lemma_tower_num_generators(data, m);

    //  Generator images are word_valid for tower(m)
    assert forall|i: int| 0 <= i < h.generator_images.len()
        implies word_valid(h.generator_images[i], h.target.num_generators)
    by {
        assert(h.generator_images[i].len() == 1);
        assert((i + k * ng) < (m + 1) * ng) by (nonlinear_arith)
            requires i < ng as int, k <= m;
    }

    //  Relator images ≡ ε: shift(relator, k*ng) ≡ ε in tower(m)
    assert forall|i: int| 0 <= i < h.source.relators.len()
        implies equiv_in_presentation(h.target,
            crate::homomorphism::apply_hom(h, h.source.relators[i]), empty_word())
    by {
        lemma_shift_hom_applies(data, k, m, h.source.relators[i]);
        //  apply_hom(h, relator) =~= shift(relator, k*ng)
        lemma_base_relator_in_tower(data, m, k, i);
        //  shift(relator, k*ng) ≡ ε in tower(m)
    }
}

///  Base at copy k embeds in tower(m): equiv(base, w1, w2) → equiv(tower(m), shift(w1, k*ng), shift(w2, k*ng)).
pub proof fn lemma_base_at_copy_k_embeds(
    data: HNNData, m: nat, k: nat, w1: Word, w2: Word,
)
    requires
        hnn_data_valid(data),
        k <= m,
        word_valid(w1, data.base.num_generators),
        word_valid(w2, data.base.num_generators),
        equiv_in_presentation(data.base, w1, w2),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            shift_word(w1, k * data.base.num_generators),
            shift_word(w2, k * data.base.num_generators)),
{
    lemma_shift_hom_valid(data, m, k);
    crate::homomorphism::lemma_hom_preserves_equiv(shift_hom(data, m, k), w1, w2);
    lemma_shift_hom_applies(data, k, m, w1);
    lemma_shift_hom_applies(data, k, m, w2);
}

//  Tower identifications_isomorphic from hnn_associations_isomorphic.
//
//  Proof uses:
//  - Backward: base_at_copy_k_embeds (shift homomorphism)
//  - Forward: lemma_afp_injectivity_right (G₂ one-shot)
//  - shift-embedding distributivity for Seq::new closure matching

///  Shift-embedding distributivity: embedding with shifted images = shift of embedding.
///  apply_embedding(shift_each(images, offset), w) =~= shift(apply_embedding(images, w), offset)
///  Shift-embedding distributivity: embedding with shifted images = shift of embedding.
///  Takes shifted_images as parameter to avoid Seq::new closure mismatch in ensures.
proof fn lemma_shift_embedding_distributes(
    images: Seq<Word>, shifted_images: Seq<Word>, w: Word, offset: nat,
)
    requires
        shifted_images.len() == images.len(),
        word_valid(w, images.len()),
        forall|i: int| 0 <= i < images.len() ==>
            #[trigger] shifted_images[i] =~= shift_word(images[i], offset),
    ensures
        apply_embedding(shifted_images, w)
            =~= shift_word(apply_embedding(images, w), offset),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        lemma_shift_embedding_distributes(images, shifted_images, w.drop_first(), offset);
        let s = w.first();
        crate::free_product::lemma_shift_concat(
            apply_embedding_symbol(images, s),
            apply_embedding(images, w.drop_first()), offset);
        //  Trigger the forall for the specific symbol index and establish symbol-level =~=
        match s {
            Symbol::Gen(i) => {
                assert(shifted_images[i as int] =~= shift_word(images[i as int], offset));
            }
            Symbol::Inv(i) => {
                assert(shifted_images[i as int] =~= shift_word(images[i as int], offset));
                crate::free_product::lemma_shift_inverse_word(images[i as int], offset);
            }
        }
    }
}

///  Tower identifications_isomorphic from hnn_associations_isomorphic.
///  Uses shift-embedding distributivity + AFP right-injectivity + base_at_copy_k_embeds.
#[verifier::rlimit(300)]
///  Forward: tower(k) equiv → base equiv for embed_a_hnn.
proof fn lemma_tower_iso_forward_mid(
    data: HNNData, k: nat, embed_a_hnn: Word,
)
    requires
        hnn_data_valid(data),
        tower_textbook_chain(data, k),
        word_valid(embed_a_hnn, data.base.num_generators),
        equiv_in_presentation(tower_presentation(data, k),
            shift_word(embed_a_hnn, k * data.base.num_generators), empty_word()),
    ensures
        equiv_in_presentation(data.base, embed_a_hnn, empty_word()),
{
    let ng = data.base.num_generators;
    reveal(presentation_valid);
    if k == 0 {
        //  tower(0) = base, shift by 0 = identity
        assert(k * ng == 0) by (nonlinear_arith) requires k == 0;
        assert(shift_word(embed_a_hnn, 0nat) =~= embed_a_hnn);
    } else {
        assert(tower_textbook_prereqs_at(data, (k - 1) as nat));
        lemma_tower_afp_data_valid(data, (k - 1) as nat);
        lemma_tower_valid(data, (k - 1) as nat);
        lemma_tower_num_generators(data, (k - 1) as nat);
        crate::normal_form_afp_textbook::lemma_afp_injectivity_right(
            tower_afp_data(data, (k - 1) as nat), embed_a_hnn);
    }
}

///  Backward: base equiv → tower(k) equiv for embed_a_hnn.
proof fn lemma_tower_iso_backward_mid(
    data: HNNData, k: nat, embed_a_hnn: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(embed_a_hnn, data.base.num_generators),
        equiv_in_presentation(data.base, embed_a_hnn, empty_word()),
    ensures
        equiv_in_presentation(tower_presentation(data, k),
            shift_word(embed_a_hnn, k * data.base.num_generators), empty_word()),
{
    //  shift(ε, k*ng) =~= ε
    assert(shift_word(empty_word(), k * data.base.num_generators) =~= empty_word());
    lemma_base_at_copy_k_embeds(data, k, k, embed_a_hnn, empty_word());
}

//  lemma_tower_iso_per_word: per-word biconditional for tower isomorphism.
//  Logic complete (forward via AFP right-injectivity + hnn_iso, backward via base_at_copy_k_embeds + hnn_iso).
//  Z3 engineering: needs explicit assertion chain connecting AFP right-injectivity output
//  (equiv(tower_afp_data(k-1).p2, embed_a_hnn, ε)) to equiv(data.base, embed_a_hnn, ε)
//  and shift(embed_a_hnn, k*ng) to embed_a_tower. ~10 more lines of intermediate assertions.
//
//  All building blocks verified (0 assumes):
//  - lemma_afp_injectivity_right ✓
//  - lemma_base_at_copy_k_embeds ✓ (shift homomorphism)
//  - lemma_shift_embedding_distributes ✓
//  - hnn_associations_isomorphic ✓ (precondition)

///  Helper: per-word proof of the tower isomorphism biconditional.
#[verifier::rlimit(1000)]
proof fn lemma_tower_iso_per_word(
    data: HNNData, k: nat, w: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        tower_textbook_chain(data, k),
        word_valid(w, data.associations.len() as nat),
    ensures ({
        let afp_data = tower_afp_data(data, k);
        let a_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].0);
        let b_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].1);
        equiv_in_presentation(afp_data.p1, apply_embedding(a_words_tower, w), empty_word())
        <==>
        equiv_in_presentation(afp_data.p2, apply_embedding(b_words_tower, w), empty_word())
    }),
{
    let ng = data.base.num_generators;
    let afp_data = tower_afp_data(data, k);
    let kk = data.associations.len();
    reveal(presentation_valid);

    assert(afp_data.identifications.len() == kk);
    let a_words_hnn = Seq::new(kk, |i: int| data.associations[i].0);
    let b_words_hnn = Seq::new(kk, |i: int| data.associations[i].1);
    //  EXACTLY match ensures clause's Seq::new (same length expression)
    let a_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].0);
    let b_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].1);

    //  Element-wise: a_words_tower[i] = shift(a_words_hnn[i], k*ng) and b_words_tower[i] = b_words_hnn[i]
    assert forall|i: int| 0 <= i < kk implies
        afp_data.identifications[i].1 == data.associations[i].1 by {}
    assert forall|i: int| 0 <= i < kk implies
        #[trigger] b_words_tower[i] =~= b_words_hnn[i] by {}
    assert(b_words_tower =~= b_words_hnn);

    //  Shift-embedding distributivity
    assert forall|i: int| 0 <= i < a_words_hnn.len() implies
        #[trigger] a_words_tower[i] =~= shift_word(a_words_hnn[i], k * ng) by {}
    lemma_shift_embedding_distributes(a_words_hnn, a_words_tower, w, k * ng);
    let embed_a_hnn = apply_embedding(a_words_hnn, w);

    //  word_valid for embed_a_hnn
    assert forall|j: int| 0 <= j < a_words_hnn.len()
        implies word_valid(#[trigger] a_words_hnn[j], ng)
    by { assert(word_valid(data.associations[j].0, ng)); }
    lemma_apply_embedding_valid(a_words_hnn, w, ng);

    let embed_a_tower = apply_embedding(a_words_tower, w);
    let embed_b_tower = apply_embedding(b_words_tower, w);

    //  Connect embed_b_tower to embed_b_hnn (shift by 0 = identity)
    assert forall|i: int| 0 <= i < b_words_hnn.len() implies
        #[trigger] b_words_tower[i] =~= shift_word(b_words_hnn[i], 0nat) by {}
    lemma_shift_embedding_distributes(b_words_hnn, b_words_tower, w, 0nat);
    //  embed_b_tower =~= shift(embed_b_hnn, 0) =~= embed_b_hnn
    assert(embed_b_tower =~= apply_embedding(b_words_hnn, w));

    //  HNN biconditional (should fire from hnn_associations_isomorphic)
    assert(equiv_in_presentation(data.base, embed_a_hnn, empty_word())
        <==> equiv_in_presentation(data.base, apply_embedding(b_words_hnn, w), empty_word()));

    //  Key =~= connections
    assert(b_words_tower =~= b_words_hnn);
    assert(embed_b_tower =~= apply_embedding(b_words_hnn, w));

    //  Explicitly trigger hnn_iso biconditional
    assert(word_valid(w, kk as nat));
    assert(equiv_in_presentation(data.base, embed_a_hnn, empty_word())
        <==> equiv_in_presentation(data.base, apply_embedding(b_words_hnn, w), empty_word()));

    //  Forward: equiv(p1, embed_a_tower, ε) → equiv(base, embed_a_hnn, ε)
    //  Then hnn_iso → equiv(base, embed_b_hnn, ε) =~= equiv(p2, embed_b_tower, ε)
    //  Setup for forward direction (AFP right-injectivity needs these)
    if k > 0 {
        assert(tower_textbook_prereqs_at(data, (k - 1) as nat));
        lemma_tower_afp_data_valid(data, (k - 1) as nat);
        lemma_tower_valid(data, (k - 1) as nat);
        lemma_tower_num_generators(data, (k - 1) as nat);
    }

    //  Establish the two intermediate biconditionals, then chain
    let mid = equiv_in_presentation(data.base, embed_a_hnn, empty_word());
    let lhs = equiv_in_presentation(afp_data.p1, apply_embedding(a_words_tower, w), empty_word());
    let rhs = equiv_in_presentation(afp_data.p2, apply_embedding(b_words_tower, w), empty_word());

    //  (1) mid ↔ rhs: from hnn_iso + embed_b connection
    //  Already have: mid ↔ equiv(base, embed_b_hnn, ε) from hnn_iso
    //  And: rhs = equiv(base, embed_b_tower, ε) = equiv(base, embed_b_hnn, ε) (from =~=)
    //  So: mid ↔ rhs

    //  (2) lhs → mid: tower equiv → base equiv
    if lhs {
        lemma_tower_iso_forward_mid(data, k, embed_a_hnn);
    }

    //  (3) mid → lhs: base equiv → tower equiv
    if mid {
        lemma_tower_iso_backward_mid(data, k, embed_a_hnn);
    }
}

pub proof fn lemma_tower_identifications_isomorphic(
    data: HNNData, k: nat,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        tower_textbook_chain(data, k),
    ensures
        crate::normal_form_amalgamated::identifications_isomorphic(tower_afp_data(data, k)),
{
    let ng = data.base.num_generators;
    let afp_data = tower_afp_data(data, k);
    let kk = afp_data.identifications.len();
    reveal(presentation_valid);

    assert(kk == data.associations.len());
    assert forall|w: Word| word_valid(w, kk as nat) implies (
        equiv_in_presentation(afp_data.p1,
            apply_embedding(Seq::new(kk, |i: int| afp_data.identifications[i].0), w),
            empty_word())
        <==>
        equiv_in_presentation(afp_data.p2,
            apply_embedding(Seq::new(kk, |i: int| afp_data.identifications[i].1), w),
            empty_word()))
    by {
        lemma_tower_iso_per_word(data, k, w);
    }
}

///  A base inverse pair [s, inv(s)] at level k: net_level is 0 and translation ≡ ε in tower.
proof fn lemma_translate_base_pair_trivial(
    data: HNNData, m: nat, s: Symbol, base_level: nat,
)
    requires
        hnn_data_valid(data),
        !is_stable(data, s),
        symbol_valid(s, data.base.num_generators),
        base_level <= m,
    ensures ({
        let pair = concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| inverse_symbol(s)));
        &&& net_level(data, pair) == 0
        &&& equiv_in_presentation(tower_presentation(data, m),
                translate_word_at(data, pair, base_level as int), empty_word())
    }),
{
    let ng = data.base.num_generators;
    let s_word = Seq::new(1, |_j: int| s);
    let inv_s_word = Seq::new(1, |_j: int| inverse_symbol(s));
    let pair = concat(s_word, inv_s_word);

    //  net_level(pair) = 0 (neither s nor inv(s) is stable)
    lemma_net_level_concat(data, s_word, inv_s_word);
    assert(s_word.first() == s);
    assert(s_word.drop_first() =~= Seq::<Symbol>::empty());
    assert(inv_s_word.first() == inverse_symbol(s));
    assert(inv_s_word.drop_first() =~= Seq::<Symbol>::empty());
    reveal_with_fuel(net_level, 2);
    assert(net_level(data, s_word) == 0) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert(net_level(data, inv_s_word) == 0) by {
        match s {
            Symbol::Gen(i) => { assert(!is_stable(data, Symbol::Inv(i))); }
            Symbol::Inv(i) => { assert(!is_stable(data, Symbol::Gen(i))); }
        }
    }

    //  Fully unfold translate for 2-element pair
    reveal_with_fuel(translate_word_at, 3);
    //  translate(pair, bl) = [shift_symbol(s, bl*ng), shift_symbol(inv(s), bl*ng)]
    //  These form a cancelling pair
    let ss = shift_symbol(s, base_level * ng);
    let iss = shift_symbol(inverse_symbol(s), base_level * ng);
    //  ss and iss are inverses: Gen(j+k) and Inv(j+k)
    assert(is_inverse_pair(ss, iss)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    //  The translated pair has a cancellation at position 0
    let translated = translate_word_at(data, pair, base_level as int);
    assert(has_cancellation_at(translated, 0));
    assert(reduce_at(translated, 0) =~= empty_word());
    //  Free reduction gives a 1-step derivation proving ≡ ε
    let step = DerivationStep::FreeReduce { position: 0 };
    assert(apply_step(tower_presentation(data, m), translated, step)
        == Some(empty_word()));
    let d = Derivation { steps: Seq::new(1, |_i: int| step) };
    assert(d.steps.len() == 1);
    assert(d.steps.first() == step);
    assert(d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
    reveal_with_fuel(derivation_produces, 2);
    assert(derivation_valid(tower_presentation(data, m), d, translated, empty_word()));
}

//  ============================================================
//  Part K: Level bounds and prefix_levels_bounded
//  ============================================================

///  All prefix net_levels of w are in [0, m].
///  This means: for every j in [0, w.len()], net_level(w[0..j]) is in [0, m].
pub open spec fn prefix_levels_bounded(data: HNNData, w: Word, m: nat) -> bool {
    forall|j: int| #![trigger w.subrange(0, j)]
        0 <= j <= w.len() ==>
            0 <= net_level(data, w.subrange(0, j)) <= m as int
}

///  Net level of a subrange [0, j] decomposes via concat.
proof fn lemma_net_level_subrange_prefix(data: HNNData, w: Word, pos: int)
    requires 0 <= pos <= w.len(),
    ensures
        w =~= concat(w.subrange(0, pos), w.subrange(pos, w.len() as int)),
        net_level(data, w) == net_level(data, w.subrange(0, pos))
            + net_level(data, w.subrange(pos, w.len() as int)),
{
    assert(w =~= w.subrange(0, pos) + w.subrange(pos, w.len() as int));
    lemma_net_level_concat(data, w.subrange(0, pos), w.subrange(pos, w.len() as int));
}

//  ============================================================
//  Part L: word_valid for shift_word at arbitrary offset
//  ============================================================

///  shift_word(w, k * ng) is word_valid for (m+1)*ng when w is base-valid and k <= m.
proof fn lemma_shift_word_valid_for_tower(
    data: HNNData, w: Word, k: nat, m: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        k <= m,
    ensures
        word_valid(shift_word(w, k * data.base.num_generators),
            (m + 1) * data.base.num_generators),
{
    let ng = data.base.num_generators;
    let sw = shift_word(w, k * ng);
    let n = (m + 1) * ng;
    //  k <= m implies k*ng <= m*ng, so i + k*ng < ng + m*ng = (m+1)*ng = n
    assert(k * ng <= m * ng) by(nonlinear_arith)
        requires k <= m
    {}
    assert(n == m * ng + ng) by(nonlinear_arith)
        requires n == (m + 1) * ng
    {}
    assert forall|j: int| 0 <= j < sw.len()
        implies symbol_valid(#[trigger] sw[j], n)
    by {
        assert(sw[j] == shift_symbol(w[j], k * ng));
        assert(symbol_valid(w[j], ng));
        match w[j] {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
    }
}

///  inverse_word(shift_word(w, k*ng)) is word_valid for tower(m).
proof fn lemma_inv_shift_word_valid_for_tower(
    data: HNNData, w: Word, k: nat, m: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        k <= m,
    ensures
        word_valid(inverse_word(shift_word(w, k * data.base.num_generators)),
            (m + 1) * data.base.num_generators),
{
    let ng = data.base.num_generators;
    lemma_shift_word_valid_for_tower(data, w, k, m);
    crate::word::lemma_inverse_word_valid(
        shift_word(w, k * ng), (m + 1) * ng);
}

//  ============================================================
//  Part M: Net level helpers for relators
//  ============================================================

///  Net level of inverse_word is the negation.
proof fn lemma_net_level_inverse(data: HNNData, w: Word)
    ensures
        net_level(data, inverse_word(w)) == -net_level(data, w),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(inverse_word(w) =~= empty_word());
    } else {
        let ng = data.base.num_generators;
        let s = w.first();
        let rest = w.drop_first();

        //  inverse_word(w) = concat(inverse_word(rest), [inv(s)])
        let inv_s_word = Seq::new(1, |_j: int| inverse_symbol(s));
        assert(inverse_word(w) =~= concat(inverse_word(rest), inv_s_word));

        //  net_level decomposes
        lemma_net_level_concat(data, inverse_word(rest), inv_s_word);
        lemma_net_level_inverse(data, rest);

        //  net_level of [inv(s)]
        assert(inv_s_word.first() == inverse_symbol(s));
        assert(inv_s_word.drop_first() =~= Seq::<Symbol>::empty());
        reveal_with_fuel(net_level, 2);

        //  Case analysis: net_level([inv(s)]) == -net_level_contribution(s)
        if s == Symbol::Gen(ng) {
            assert(inverse_symbol(s) == Symbol::Inv(ng));
        } else if s == Symbol::Inv(ng) {
            assert(inverse_symbol(s) == Symbol::Gen(ng));
        } else {
            match s {
                Symbol::Gen(i) => {
                    assert(i != ng);
                    assert(inverse_symbol(s) == Symbol::Inv(i));
                    assert(Symbol::Inv(i) != Symbol::Gen(ng));
                    assert(Symbol::Inv(i) != Symbol::Inv(ng));
                }
                Symbol::Inv(i) => {
                    assert(i != ng);
                    assert(inverse_symbol(s) == Symbol::Gen(i));
                    assert(Symbol::Gen(i) != Symbol::Gen(ng));
                    assert(Symbol::Gen(i) != Symbol::Inv(ng));
                }
            }
        }
    }
}

///  HNN relator has net_level 0.
proof fn lemma_net_level_hnn_relator(data: HNNData, i: int)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
    ensures
        net_level(data, hnn_relator(data, i)) == 0,
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    let t_inv = Seq::new(1, |_j: int| Symbol::Inv(ng));
    let t_gen = Seq::new(1, |_j: int| Symbol::Gen(ng));
    let part1 = concat(t_inv, a_i);
    let part2 = concat(t_gen, inverse_word(b_i));

    assert(hnn_relator(data, i) =~= concat(part1, part2));
    lemma_net_level_concat(data, part1, part2);
    lemma_net_level_concat(data, t_inv, a_i);
    lemma_net_level_concat(data, t_gen, inverse_word(b_i));
    lemma_net_level_stable(data, Symbol::Inv(ng));
    lemma_net_level_stable(data, Symbol::Gen(ng));
    lemma_net_level_base_word(data, a_i);
    crate::word::lemma_inverse_word_valid(b_i, ng);
    lemma_net_level_base_word(data, inverse_word(b_i));
}

///  Any relator in hnn_presentation has net_level 0.
proof fn lemma_net_level_hnn_pres_relator(data: HNNData, idx: int)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
    ensures
        net_level(data, hnn_presentation(data).relators[idx]) == 0,
{
    let p = hnn_presentation(data);
    let nb = data.base.relators.len();
    if idx < nb {
        assert(p.relators[idx] == data.base.relators[idx]);
        reveal(presentation_valid);
        lemma_net_level_base_word(data, data.base.relators[idx]);
    } else {
        let hi = (idx - nb) as int;
        assert(p.relators[idx] == hnn_relator(data, hi));
        lemma_net_level_hnn_relator(data, hi);
    }
}

///  get_relator has net_level 0 when the underlying relator does.
proof fn lemma_net_level_get_relator(data: HNNData, idx: nat, inverted: bool)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
    ensures
        net_level(data, get_relator(hnn_presentation(data), idx, inverted)) == 0,
{
    let p = hnn_presentation(data);
    lemma_net_level_hnn_pres_relator(data, idx as int);
    if inverted {
        lemma_net_level_inverse(data, p.relators[idx as int]);
    }
}

///  Decompose inverse_word(hnn_relator):
///  inv(t⁻¹ · a_i · t · inv(b_i)) = b_i · t⁻¹ · inv(a_i) · t
proof fn lemma_inverse_hnn_relator_decomp(data: HNNData, i: int)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
    ensures ({
        let ng = data.base.num_generators;
        let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
        let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
        let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
        inverse_word(hnn_relator(data, i)) =~=
            concat(b_i, concat(t_inv_word, concat(inverse_word(a_i), t_word)))
    }),
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
    let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
    let inv_b_i = inverse_word(b_i);

    //  hnn_relator = concat(t_inv_word, concat(a_i, concat(t_word, inv_b_i)))
    let r = hnn_relator(data, i);
    assert(r =~= concat(t_inv_word, concat(a_i, concat(t_word, inv_b_i))));

    //  Apply inverse_concat repeatedly
    crate::word::lemma_inverse_concat(t_inv_word, concat(a_i, concat(t_word, inv_b_i)));
    crate::word::lemma_inverse_concat(a_i, concat(t_word, inv_b_i));
    crate::word::lemma_inverse_concat(t_word, inv_b_i);

    //  inverse of single-symbol words
    assert(inverse_word(t_inv_word) =~= t_word) by {
        reveal_with_fuel(inverse_word, 2);
    }
    assert(inverse_word(t_word) =~= t_inv_word) by {
        reveal_with_fuel(inverse_word, 2);
    }

    //  inverse of inverse_word(b_i) = b_i
    crate::word::lemma_inverse_involution(b_i);

    //  Chain: inv(r) = inv(inv_b_i) ++ inv(t_word) ++ inv(a_i) ++ inv(t_inv_word)
    //                = b_i ++ t_inv_word ++ inv(a_i) ++ t_word
}

//  ============================================================
//  Part N: Per-step translation — the core case analysis
//  ============================================================

///  Helper: A single free-reduce or free-expand step preserves translation equivalence.
///  The inverse pair [s, inv(s)] either:
///   - stable pair: translates to ε (=~=)
///   - base pair: translates to a cancelling pair ≡ ε in tower
proof fn lemma_pair_translate_equiv_empty(
    data: HNNData, m: nat, s: Symbol, base_level: int,
)
    requires
        hnn_data_valid(data),
        symbol_valid(s, hnn_presentation(data).num_generators),
        0 <= base_level <= m as int,
    ensures ({
        let pair = concat(Seq::new(1, |_j: int| s),
                          Seq::new(1, |_j: int| inverse_symbol(s)));
        &&& net_level(data, pair) == 0
        &&& equiv_in_presentation(tower_presentation(data, m),
                translate_word_at(data, pair, base_level), empty_word())
        &&& word_valid(translate_word_at(data, pair, base_level),
                tower_presentation(data, m).num_generators)
    }),
{
    let ng = data.base.num_generators;
    let pair = concat(Seq::new(1, |_j: int| s),
                      Seq::new(1, |_j: int| inverse_symbol(s)));
    let tp = tower_presentation(data, m);

    if is_stable(data, s) {
        //  Stable pair: translate =~= ε
        lemma_translate_stable_pair(data, s, base_level);
        assert(translate_word_at(data, pair, base_level) =~= empty_word());
        //  empty word ≡ ε trivially
        lemma_equiv_refl(tp, empty_word());
        //  word_valid of empty word
        assert(word_valid(empty_word(), tp.num_generators));
    } else {
        //  Base pair: use existing lemma
        assert(symbol_valid(s, ng)) by {
            match s {
                Symbol::Gen(i) => { assert(i < ng + 1); assert(i != ng); assert(i < ng); }
                Symbol::Inv(i) => { assert(i < ng + 1); assert(i != ng); assert(i < ng); }
            }
        }
        lemma_translate_base_pair_trivial(data, m, s, base_level as nat);

        //  word_valid: the translated pair is a 2-symbol word with shifted symbols
        lemma_tower_num_generators(data, m);
        reveal_with_fuel(translate_word_at, 3);
        let translated = translate_word_at(data, pair, base_level);
        let bl = base_level as nat;
        assert(bl * ng <= m * ng) by(nonlinear_arith)
            requires bl <= m
        {}
        assert((m + 1) * ng == m * ng + ng) by(nonlinear_arith) {}
        assert forall|j: int| 0 <= j < translated.len()
            implies symbol_valid(#[trigger] translated[j], tp.num_generators)
        by {
            match s {
                Symbol::Gen(i) => { assert(i < ng); }
                Symbol::Inv(i) => { assert(i < ng); }
            }
        }
    }
}

///  Helper: word_valid for the translation of a base relator at level k.
proof fn lemma_translate_base_relator_valid(
    data: HNNData, m: nat, k: nat, r_idx: int,
)
    requires
        hnn_data_valid(data),
        0 <= r_idx < data.base.relators.len(),
        k <= m,
    ensures
        word_valid(
            translate_word_at(data, data.base.relators[r_idx], k as int),
            tower_presentation(data, m).num_generators),
{
    let ng = data.base.num_generators;
    let r = data.base.relators[r_idx];
    reveal(presentation_valid);
    lemma_translate_base_word_at(data, r, k);
    lemma_tower_num_generators(data, m);
    lemma_shift_word_valid_for_tower(data, r, k, m);
}

///  Helper: word_valid for the translation of an HNN relator at level k.
proof fn lemma_translate_hnn_relator_valid(
    data: HNNData, m: nat, k: nat, i: int,
)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
        k >= 1,
        k <= m,
    ensures
        word_valid(
            translate_word_at(data, hnn_relator(data, i), k as int),
            tower_presentation(data, m).num_generators),
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    lemma_translate_hnn_relator(data, i, k as int);
    lemma_tower_num_generators(data, m);
    //  translate = amalgamation_relator(tower_afp_data(data, (k-1)), i)
    //            = concat(shift_word(a_i, (k-1)*ng), inverse_word(shift_word(b_i, k*ng)))
    let afp_data = tower_afp_data(data, (k - 1) as nat);
    let tr = amalgamation_relator(afp_data, i);
    assert(translate_word_at(data, hnn_relator(data, i), k as int) =~= tr);

    //  Need tower_num_generators at k-1 to connect afp_data.p1.num_generators = k*ng
    lemma_tower_num_generators(data, (k - 1) as nat);

    let sa = shift_word(a_i, ((k - 1) as nat) * ng);
    crate::word::lemma_inverse_word_valid(b_i, ng);
    let sb = shift_word(b_i, k * ng);
    let inv_sb = inverse_word(sb);

    let tp = tower_presentation(data, m);
    lemma_shift_word_valid_for_tower(data, a_i, (k - 1) as nat, m);
    lemma_shift_word_valid_for_tower(data, b_i, k, m);
    crate::word::lemma_inverse_word_valid(sb, (m + 1) * ng);
    crate::word::lemma_concat_word_valid(sa, inv_sb, (m + 1) * ng);

    //  Connect tr to concat(sa, inv_sb) via afp_data decomposition
    assert(afp_data.p1.num_generators == k * ng);
    assert(tr =~= concat(sa, inv_sb));

    //  Transfer word_valid through =~= to the translate
    let tw = translate_word_at(data, hnn_relator(data, i), k as int);
    assert forall|j: int| 0 <= j < tw.len()
        implies symbol_valid(#[trigger] tw[j], tp.num_generators)
    by {
        assert(tw[j] == tr[j]);
    }
}

///  Helper: translated relator (base or HNN, possibly inverted) is word_valid for tower(m).
proof fn lemma_translate_relator_valid(
    data: HNNData, m: nat, idx: nat, inverted: bool, level: int,
)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
        0 <= level <= m as int,
        //  HNN relators need level >= 1
        idx >= data.base.relators.len() ==> level >= 1,
    ensures
        word_valid(
            translate_word_at(data,
                get_relator(hnn_presentation(data), idx, inverted), level),
            tower_presentation(data, m).num_generators),
{
    let p = hnn_presentation(data);
    let ng = data.base.num_generators;
    let nb = data.base.relators.len();
    let tp = tower_presentation(data, m);

    lemma_tower_num_generators(data, m);
    lemma_tower_valid(data, m);

    if !inverted {
        if idx < nb {
            //  Base relator
            assert(p.relators[idx as int] == data.base.relators[idx as int]);
            lemma_translate_base_relator_valid(data, m, level as nat, idx as int);
        } else {
            //  HNN relator
            let hi = (idx - nb) as int;
            assert(p.relators[idx as int] == hnn_relator(data, hi));
            lemma_translate_hnn_relator_valid(data, m, level as nat, hi);
        }
    } else {
        //  Inverted relator: get_relator = inverse_word(p.relators[idx])
        if idx < nb {
            //  Inverted base relator: inverse_word of a base word is still base-valid
            assert(p.relators[idx as int] == data.base.relators[idx as int]);
            let base_r = data.base.relators[idx as int];
            reveal(presentation_valid);
            crate::word::lemma_inverse_word_valid(base_r, ng);
            lemma_translate_base_word_at(data, inverse_word(base_r), level as nat);
            lemma_tower_num_generators(data, m);
            lemma_shift_word_valid_for_tower(data, inverse_word(base_r), level as nat, m);
        } else {
            //  Inverted HNN relator: inv(t⁻¹·a_i·t·inv(b_i)) = b_i·t⁻¹·inv(a_i)·t
            let hi = (idx - nb) as int;
            assert(p.relators[idx as int] == hnn_relator(data, hi));
            lemma_inverse_hnn_relator_decomp(data, hi);
            let (a_i, b_i) = (data.associations[hi].0, data.associations[hi].1);
            let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
            let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
            crate::word::lemma_inverse_word_valid(a_i, ng);
            let inv_a_i = inverse_word(a_i);
            let k = level as nat;

            //  Decompose and translate each part
            let part_a = b_i;
            let part_b = t_inv_word;
            let part_c = inv_a_i;
            let part_d = t_word;
            let part_cd = concat(part_c, part_d);
            let part_bcd = concat(part_b, part_cd);

            assert(inverse_word(hnn_relator(data, hi))
                =~= concat(part_a, part_bcd));

            //  net_level computations
            lemma_net_level_base_word(data, b_i);
            lemma_net_level_base_word(data, inv_a_i);
            lemma_net_level_stable(data, Symbol::Inv(ng));
            lemma_net_level_stable(data, Symbol::Gen(ng));
            lemma_net_level_concat(data, part_c, part_d);
            lemma_net_level_concat(data, part_b, part_cd);

            //  translate_concat decompositions
            lemma_translate_concat(data, part_a, part_bcd, k as int);
            lemma_translate_concat(data, part_b, part_cd, k as int);
            lemma_translate_concat(data, part_c, part_d, (k - 1) as int);
            lemma_translate_base_word_at(data, b_i, k);
            lemma_translate_stable_empty(data, Symbol::Inv(ng), k as int);
            lemma_translate_base_word_at(data, inv_a_i, (k - 1) as nat);
            lemma_translate_stable_empty(data, Symbol::Gen(ng), (k - 1) as int);

            let tr = translate_word_at(data, inverse_word(hnn_relator(data, hi)), k as int);
            assert(tr =~= concat(
                shift_word(b_i, k * ng),
                shift_word(inv_a_i, ((k - 1) as nat) * ng)));

            //  word_valid of the translated parts
            lemma_shift_word_valid_for_tower(data, b_i, k, m);
            lemma_shift_word_valid_for_tower(data, inv_a_i, (k - 1) as nat, m);
            crate::word::lemma_concat_word_valid(
                shift_word(b_i, k * ng),
                shift_word(inv_a_i, ((k - 1) as nat) * ng),
                (m + 1) * ng);
        }
    }
}

///  Helper: translated relator (base or HNN, possibly inverted) ≡ ε in tower(m).
proof fn lemma_translate_relator_equiv_empty(
    data: HNNData, m: nat, idx: nat, inverted: bool, level: int,
)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
        0 <= level <= m as int,
        idx >= data.base.relators.len() ==> level >= 1,
    ensures ({
        let r = get_relator(hnn_presentation(data), idx, inverted);
        &&& net_level(data, r) == 0
        &&& equiv_in_presentation(tower_presentation(data, m),
                translate_word_at(data, r, level), empty_word())
    }),
{
    let p = hnn_presentation(data);
    let ng = data.base.num_generators;
    let nb = data.base.relators.len();
    let tp = tower_presentation(data, m);
    let r = get_relator(p, idx, inverted);

    lemma_net_level_get_relator(data, idx, inverted);

    if !inverted {
        if idx < nb {
            //  Base relator at level k
            assert(r == data.base.relators[idx as int]);
            reveal(presentation_valid);
            lemma_translate_base_word_at(data, r, level as nat);
            lemma_base_relator_in_tower(data, m, level as nat, idx as int);
        } else {
            //  HNN relator at level k
            let hi = (idx - nb) as int;
            assert(r == hnn_relator(data, hi));
            lemma_translate_hnn_relator(data, hi, level);
            lemma_ident_relator_in_tower(data, m, (level - 1) as nat, hi);
        }
    } else {
        //  Inverted: get_relator = inverse_word(relator)
        if idx < nb {
            assert(r == inverse_word(data.base.relators[idx as int]));
            let base_r = data.base.relators[idx as int];
            reveal(presentation_valid);
            //  First show non-inverted translate ≡ ε
            lemma_translate_base_word_at(data, base_r, level as nat);
            lemma_base_relator_in_tower(data, m, level as nat, idx as int);

            //  Now show inverted: inverse_word(base_r) is still base-valid
            crate::word::lemma_inverse_word_valid(base_r, ng);
            lemma_translate_base_word_at(data, inverse_word(base_r), level as nat);

            //  shift(inv(r), k*ng) = inv(shift(r, k*ng))
            crate::free_product::lemma_shift_inverse_word(base_r, (level as nat) * ng);

            //  translate(inv(r), k) =~= inv(shift(r, k*ng)) and translate(r, k) ≡ ε
            //  so inv(translate(r, k)) ≡ ε
            lemma_tower_valid(data, m);
            lemma_tower_num_generators(data, m);
            lemma_shift_word_valid_for_tower(data, base_r, level as nat, m);
            crate::normal_form_amalgamated::lemma_inverse_of_trivial(
                tp,
                shift_word(base_r, (level as nat) * ng));
        } else {
            let hi = (idx - nb) as int;
            assert(r == inverse_word(hnn_relator(data, hi)));
            //  Decompose inv(hnn_relator) = b_i · t⁻¹ · inv(a_i) · t
            lemma_inverse_hnn_relator_decomp(data, hi);
            let (a_i, b_i) = (data.associations[hi].0, data.associations[hi].1);
            let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
            let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
            crate::word::lemma_inverse_word_valid(a_i, ng);
            let inv_a_i = inverse_word(a_i);
            let k = level as nat;

            let part_a = b_i;
            let part_b = t_inv_word;
            let part_c = inv_a_i;
            let part_d = t_word;
            let part_cd = concat(part_c, part_d);
            let part_bcd = concat(part_b, part_cd);

            assert(r =~= concat(part_a, part_bcd));

            //  net_level and translate decomposition
            lemma_net_level_base_word(data, b_i);
            lemma_net_level_base_word(data, inv_a_i);
            lemma_net_level_stable(data, Symbol::Inv(ng));
            lemma_net_level_stable(data, Symbol::Gen(ng));
            lemma_net_level_concat(data, part_c, part_d);
            lemma_net_level_concat(data, part_b, part_cd);
            lemma_translate_concat(data, part_a, part_bcd, k as int);
            lemma_translate_concat(data, part_b, part_cd, k as int);
            lemma_translate_concat(data, part_c, part_d, (k - 1) as int);
            lemma_translate_base_word_at(data, b_i, k);
            lemma_translate_stable_empty(data, Symbol::Inv(ng), k as int);
            lemma_translate_base_word_at(data, inv_a_i, (k - 1) as nat);
            lemma_translate_stable_empty(data, Symbol::Gen(ng), (k - 1) as int);

            //  translate(r, k) =~= concat(shift(b_i, k*ng), shift(inv(a_i), (k-1)*ng))
            let tr_inv = translate_word_at(data, r, k as int);
            assert(tr_inv =~= concat(
                shift_word(b_i, k * ng),
                shift_word(inv_a_i, ((k - 1) as nat) * ng)));

            //  This equals inverse_word(amalgamation_relator(afp_data, hi))
            //  amal_r = concat(shift(a_i, (k-1)*ng), inv(shift(b_i, k*ng)))
            //  inv(amal_r) = concat(shift(b_i, k*ng), inv(shift(a_i, (k-1)*ng)))
            crate::free_product::lemma_shift_inverse_word(a_i, ((k - 1) as nat) * ng);
            //  shift(inv(a_i), (k-1)*ng) =~= inv(shift(a_i, (k-1)*ng))

            //  amal_r ≡ ε, so inv(amal_r) ≡ ε
            let afp_data = tower_afp_data(data, (level - 1) as nat);
            let amal_r = amalgamation_relator(afp_data, hi);
            lemma_translate_hnn_relator(data, hi, level);
            lemma_ident_relator_in_tower(data, m, (level - 1) as nat, hi);

            lemma_tower_valid(data, m);
            lemma_tower_num_generators(data, m);

            //  word_valid of amal_r for lemma_inverse_of_trivial
            lemma_tower_num_generators(data, (level - 1) as nat);
            let sa = shift_word(a_i, ((k - 1) as nat) * ng);
            let sb = shift_word(b_i, k * ng);
            lemma_shift_word_valid_for_tower(data, a_i, (k - 1) as nat, m);
            lemma_shift_word_valid_for_tower(data, b_i, k, m);
            crate::word::lemma_inverse_word_valid(sb, (m + 1) * ng);
            crate::word::lemma_concat_word_valid(sa, inverse_word(sb), (m + 1) * ng);
            //  amal_r =~= concat(sa, inverse_word(sb))
            assert(amal_r =~= concat(sa, inverse_word(sb)));
            //  Transfer word_valid through =~=
            assert forall|j: int| 0 <= j < amal_r.len()
                implies symbol_valid(#[trigger] amal_r[j], tp.num_generators)
            by {
                let cv = concat(sa, inverse_word(sb));
                assert(amal_r[j] == cv[j]);
            }

            crate::normal_form_amalgamated::lemma_inverse_of_trivial(tp, amal_r);
            //  inv(amal_r) = inv(concat(sa, inv(sb))) =~= concat(inv(inv(sb)), inv(sa)) =~= concat(sb, inv(sa))
            crate::word::lemma_inverse_concat(sa, inverse_word(sb));
            crate::word::lemma_inverse_involution(sb);
            //  inv(sa) =~= shift(inv(a_i), (k-1)*ng)
            crate::free_product::lemma_shift_inverse_word(a_i, ((k - 1) as nat) * ng);
            assert(inverse_word(amal_r) =~= concat(sb, shift_word(inv_a_i, ((k - 1) as nat) * ng)));
            assert(tr_inv =~= inverse_word(amal_r));
        }
    }
}

//  ============================================================
//  Part O: The per-step lemma
//  ============================================================

///  For FreeReduce/RelatorDelete at position pos:
///  the level at pos determines the middle's translation.
///  Need: 0 <= net_level(prefix) <= m, and for HNN relators, >= 1.
///
///  For FreeExpand/RelatorInsert at position pos:
///  the level at pos determines the middle's translation.
///  Same level requirements.
///
///  In all cases: translate(w) ≡ translate(w_next) in tower(m).
pub proof fn lemma_hnn_step_tower_equiv(
    data: HNNData, m: nat, base_level: int, w: Word, step: DerivationStep,
)
    requires
        hnn_data_valid(data),
        word_valid(w, hnn_presentation(data).num_generators),
        apply_step(hnn_presentation(data), w, step) is Some,
        step_level_ok(data, m, base_level, w, step),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, w, base_level),
            translate_word_at(data, apply_step(hnn_presentation(data), w, step).unwrap(), base_level)),
{
    let p = hnn_presentation(data);
    let tp = tower_presentation(data, m);
    let w_next = apply_step(p, w, step).unwrap();
    lemma_tower_valid(data, m);
    lemma_tower_num_generators(data, m);

    match step {
        DerivationStep::FreeReduce { position } => {
            let pos = position;
            let s = w[pos];
            let prefix = w.subrange(0, pos);
            let middle = concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| w[pos + 1]));
            let suffix = w.subrange(pos + 2, w.len() as int);

            assert(w =~= concat(prefix, concat(middle, suffix)));
            assert(w_next =~= concat(prefix, suffix));

            assert(is_inverse_pair(w[pos], w[pos + 1]));
            assert(w[pos + 1] == inverse_symbol(s));
            assert(middle =~= concat(Seq::new(1, |_j: int| s),
                                      Seq::new(1, |_j: int| inverse_symbol(s))));

            let level = base_level + net_level(data, prefix);

            assert(symbol_valid(s, p.num_generators));

            lemma_pair_translate_equiv_empty(data, m, s, level);

            lemma_translate_delete_middle(data, m, base_level, prefix, middle, suffix);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let pos = position;
            let prefix = w.subrange(0, pos);
            let suffix = w.subrange(pos, w.len() as int);
            let middle = concat(Seq::new(1, |_j: int| symbol),
                                Seq::new(1, |_j: int| inverse_symbol(symbol)));

            assert(w =~= concat(prefix, suffix));
            assert(w_next =~= concat(prefix, concat(middle, suffix)));

            let level = base_level + net_level(data, prefix);
            lemma_pair_translate_equiv_empty(data, m, symbol, level);

            lemma_translate_insert_middle(data, m, base_level, prefix, middle, suffix);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let pos = position;
            let r = get_relator(p, relator_index, inverted);
            let prefix = w.subrange(0, pos);
            let middle = r;
            let suffix = w.subrange(pos + r.len(), w.len() as int);

            assert(w.subrange(pos, pos + r.len() as int) == r);
            assert(w =~= concat(prefix, concat(middle, suffix)));
            assert(w_next =~= concat(prefix, suffix));

            let level = base_level + net_level(data, prefix);

            lemma_translate_relator_equiv_empty(data, m, relator_index, inverted, level);
            lemma_translate_relator_valid(data, m, relator_index, inverted, level);

            lemma_translate_delete_middle(data, m, base_level, prefix, middle, suffix);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let pos = position;
            let r = get_relator(p, relator_index, inverted);
            let prefix = w.subrange(0, pos);
            let suffix = w.subrange(pos, w.len() as int);
            let middle = r;

            assert(w =~= concat(prefix, suffix));
            assert(w_next =~= concat(prefix, concat(middle, suffix)));

            let level = base_level + net_level(data, prefix);

            lemma_translate_relator_equiv_empty(data, m, relator_index, inverted, level);
            lemma_translate_relator_valid(data, m, relator_index, inverted, level);

            lemma_translate_insert_middle(data, m, base_level, prefix, middle, suffix);
        },
    }
}

//  ============================================================
//  Part P: Derivation-level induction
//  ============================================================

///  Get the position of a derivation step.
pub open spec fn step_position(step: DerivationStep) -> int {
    match step {
        DerivationStep::FreeReduce { position } => position,
        DerivationStep::FreeExpand { position, .. } => position,
        DerivationStep::RelatorInsert { position, .. } => position,
        DerivationStep::RelatorDelete { position, .. } => position,
    }
}

///  Whether a step involves an HNN relator (not a base relator).
pub open spec fn step_is_hnn_relator(data: HNNData, step: DerivationStep) -> bool {
    match step {
        DerivationStep::RelatorInsert { relator_index, .. } |
        DerivationStep::RelatorDelete { relator_index, .. } =>
            relator_index >= data.base.relators.len(),
        _ => false,
    }
}

///  Level condition for a single step applied to word w.
pub open spec fn step_level_ok(data: HNNData, m: nat, base_level: int, w: Word, step: DerivationStep) -> bool {
    let pos = step_position(step);
    let level = net_level(data, w.subrange(0, pos)) + base_level;
    &&& 0 <= level <= m as int
    &&& (step_is_hnn_relator(data, step) ==> level >= 1)
}

///  A full derivation from w producing w', where every step has valid levels.
///  Returns the final word (should equal w') when the derivation is valid.
pub open spec fn derivation_levels_ok(
    data: HNNData, m: nat, base_level: int,
    steps: Seq<DerivationStep>, start: Word,
) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 {
        true
    } else {
        let p = hnn_presentation(data);
        match apply_step(p, start, steps.first()) {
            Some(next) => {
                step_level_ok(data, m, base_level, start, steps.first())
                && derivation_levels_ok(data, m, base_level, steps.drop_first(), next)
            },
            None => false,
        }
    }
}

///  Main induction: if all steps in a derivation have valid (shifted) levels,
///  then translate_at(start, base_level) ≡ translate_at(end, base_level) in tower(m).
pub proof fn lemma_hnn_derivation_to_tower_equiv(
    data: HNNData, m: nat, base_level: int,
    steps: Seq<DerivationStep>, start: Word, end: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(start, hnn_presentation(data).num_generators),
        derivation_produces(hnn_presentation(data), steps, start) == Some(end),
        derivation_levels_ok(data, m, base_level, steps, start),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, start, base_level),
            translate_word_at(data, end, base_level)),
    decreases steps.len(),
{
    let p = hnn_presentation(data);
    let tp = tower_presentation(data, m);

    if steps.len() == 0 {
        assert(start == end);
        lemma_equiv_refl(tp, translate_word_at(data, start, base_level));
    } else {
        let step = steps.first();
        let mid = apply_step(p, start, step).unwrap();

        //  Per-step: translate(start) ≡ translate(mid)
        lemma_hnn_step_tower_equiv(data, m, base_level, start, step);

        //  mid is word_valid (step preserves word_valid)
        lemma_hnn_presentation_valid(data);
        crate::presentation::lemma_step_preserves_word_valid_pres(p, start, step, mid);

        //  Inductive: translate(mid) ≡ translate(end)
        lemma_hnn_derivation_to_tower_equiv(data, m, base_level, steps.drop_first(), mid, end);

        //  Chain: translate(start) ≡ translate(end)
        lemma_equiv_transitive(tp,
            translate_word_at(data, start, base_level),
            translate_word_at(data, mid, base_level),
            translate_word_at(data, end, base_level));
    }
}

///  **Britton's Lemma (Lyndon-Schupp Ch. IV):**
///  If w is a base word (no stable letters) and w ≡ ε in the HNN extension G*,
///  then w ≡ ε in the base group G.
///
///  Proof:
///  1. w ≡ ε in G* → derivation D with levels fitting in tower(m)
///  2. lemma_hnn_derivation_to_tower_equiv → translate(w) ≡ translate(ε) in tower(m)
///  3. translate(w) = w (base word), translate(ε) = ε
///  4. lemma_g0_embeds_in_tower_textbook → w ≡ ε in G
pub proof fn britton_lemma(
    data: HNNData, m: nat, w: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
        //  The derivation fits within tower height m (at base_level 0)
        ({
            let d: Derivation = choose|d: Derivation|
                derivation_valid(hnn_presentation(data), d, w, empty_word());
            derivation_levels_ok(data, m, 0, d.steps, w)
        }),
        //  Tower textbook prerequisites
        tower_textbook_chain(data, m),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
    let hp = hnn_presentation(data);
    let d: Derivation = choose|d: Derivation|
        derivation_valid(hp, d, w, empty_word());

    assert(word_valid(w, hp.num_generators)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies symbol_valid(#[trigger] w[k], hp.num_generators)
        by {}
    }

    lemma_hnn_derivation_to_tower_equiv(data, m, 0, d.steps, w, empty_word());

    lemma_translate_base_word(data, w);
    lemma_translate_empty(data);

    lemma_g0_embeds_in_tower_textbook(data, m, w);
}

//  ============================================================
//  Part S: Derivation level bounds for shifted translation
//  ============================================================

///  Minimum "adjusted" step level across a derivation.
///  For HNN relator steps, returns level - 1 (since they need level >= 1).
///  For other steps, returns level (since they need level >= 0).
///  Shift >= -derivation_min_adj_level ensures all shifted levels are valid.
pub open spec fn derivation_min_adj_level(
    data: HNNData, steps: Seq<DerivationStep>, start: Word,
) -> int
    decreases steps.len(),
{
    let hp = hnn_presentation(data);
    if steps.len() == 0 { 0 }
    else {
        match apply_step(hp, start, steps.first()) {
            Some(next) => {
                let pos = step_position(steps.first());
                let level = net_level(data, start.subrange(0, pos));
                let adj = if step_is_hnn_relator(data, steps.first()) { level - 1 } else { level };
                let rest_min = derivation_min_adj_level(data, steps.drop_first(), next);
                if adj < rest_min { adj } else { rest_min }
            }
            None => 0
        }
    }
}

///  Maximum step level across a derivation.
pub open spec fn derivation_max_step_level(
    data: HNNData, steps: Seq<DerivationStep>, start: Word,
) -> int
    decreases steps.len(),
{
    let hp = hnn_presentation(data);
    if steps.len() == 0 { 0 }
    else {
        match apply_step(hp, start, steps.first()) {
            Some(next) => {
                let pos = step_position(steps.first());
                let level = net_level(data, start.subrange(0, pos));
                let rest_max = derivation_max_step_level(data, steps.drop_first(), next);
                if level > rest_max { level } else { rest_max }
            }
            None => 0
        }
    }
}

///  If base_level >= -min_adj and m >= max_level + base_level,
///  then derivation_levels_ok holds.
proof fn lemma_derivation_levels_ok_from_bounds(
    data: HNNData, m: nat, base_level: int,
    steps: Seq<DerivationStep>, start: Word,
)
    requires
        derivation_produces(hnn_presentation(data), steps, start) is Some,
        base_level >= -derivation_min_adj_level(data, steps, start),
        m as int >= derivation_max_step_level(data, steps, start) + base_level,
    ensures
        derivation_levels_ok(data, m, base_level, steps, start),
    decreases steps.len(),
{
    if steps.len() == 0 {} else {
        let hp = hnn_presentation(data);
        let step = steps.first();
        let next = apply_step(hp, start, step).unwrap();
        let pos = step_position(step);
        let level = net_level(data, start.subrange(0, pos));
        let adj = if step_is_hnn_relator(data, step) { level - 1 } else { level };

        //  adj >= derivation_min_adj_level, so base_level >= -adj, so level + base_level >= 0 (or >= 1)
        assert(adj >= derivation_min_adj_level(data, steps, start));
        //  level <= derivation_max_step_level, so level + base_level <= m
        assert(level <= derivation_max_step_level(data, steps, start));

        //  Recurse: rest_min >= whole_min and rest_max <= whole_max
        let rest_min = derivation_min_adj_level(data, steps.drop_first(), next);
        let rest_max = derivation_max_step_level(data, steps.drop_first(), next);
        assert(rest_min >= derivation_min_adj_level(data, steps, start)) by {
            if adj < rest_min {} else {}
        }
        assert(rest_max <= derivation_max_step_level(data, steps, start)) by {
            if level > rest_max {} else {}
        }

        lemma_derivation_levels_ok_from_bounds(data, m, base_level, steps.drop_first(), next);
    }
}

//  ============================================================
//  Part T: Tower textbook chain from HNN associations
//  ============================================================

///  Derive tower_textbook_chain from hnn_associations_isomorphic by induction.
pub proof fn lemma_tower_textbook_chain_from_hnn_iso(data: HNNData, m: nat)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
    ensures
        tower_textbook_chain(data, m),
    decreases m,
{
    if m == 0 {
        assert forall|k: nat| k < 0nat
            implies #[trigger] tower_textbook_prereqs_at(data, k) by {}
    } else {
        //  IH: tower_textbook_chain(data, m-1)
        lemma_tower_textbook_chain_from_hnn_iso(data, (m - 1) as nat);

        let k = (m - 1) as nat;
        let afp_data = tower_afp_data(data, k);

        //  Prove identifications_isomorphic at level k
        lemma_tower_identifications_isomorphic(data, k);

        //  Prove action_preserves_canonical at level k
        lemma_tower_afp_data_valid(data, k);
        lemma_tower_valid(data, k);
        reveal(presentation_valid);
        crate::normal_form_afp_textbook::lemma_iso_implies_apc(afp_data);

        assert(tower_textbook_prereqs_at(data, k));

        assert forall|j: nat| j < m
            implies #[trigger] tower_textbook_prereqs_at(data, j)
        by {
            if j < k {} //  from IH
        }
    }
}

//  ============================================================
//  Part U: Copy-s tower embedding
//  ============================================================

///  Generalized tower embedding: if shift(w, s*ng) ≡ ε in tower(m) where s <= m,
///  then w ≡ ε in base. Uses AFP left-injectivity to peel from tower(m) down to
///  tower(s), then AFP right-injectivity at level s-1.
pub proof fn lemma_copy_s_embeds(data: HNNData, m: nat, s: nat, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        s <= m,
        tower_textbook_chain(data, m),
        equiv_in_presentation(tower_presentation(data, m),
            shift_word(w, s * data.base.num_generators), empty_word()),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
    decreases m,
{
    let ng = data.base.num_generators;
    if m == 0 {
        assert(s == 0);
        assert(s * ng == 0) by (nonlinear_arith) requires s == 0;
        assert(shift_word(w, 0nat) =~= w);
    } else if s == m {
        //  shift(w, m*ng) is in the G₂ part of AFP at level m-1
        let prev = (m - 1) as nat;
        assert(tower_textbook_prereqs_at(data, prev));
        lemma_tower_afp_data_valid(data, prev);
        lemma_tower_valid(data, prev);
        lemma_tower_num_generators(data, prev);
        reveal(presentation_valid);
        crate::normal_form_afp_textbook::lemma_afp_injectivity_right(
            tower_afp_data(data, prev), w);
    } else {
        //  s < m: shift(w, s*ng) is a tower(m-1) word
        let prev = (m - 1) as nat;
        assert(tower_textbook_prereqs_at(data, prev));
        lemma_tower_afp_data_valid(data, prev);
        lemma_tower_valid(data, prev);
        lemma_tower_num_generators(data, prev);
        reveal(presentation_valid);

        lemma_shift_word_valid_for_tower(data, w, s, prev);
        crate::normal_form_afp_textbook::lemma_afp_injectivity(
            tower_afp_data(data, prev), shift_word(w, s * ng));

        assert(tower_textbook_chain(data, prev)) by {
            assert forall|k: nat| k < prev
                implies #[trigger] tower_textbook_prereqs_at(data, k)
            by { assert(k < m); }
        }
        lemma_copy_s_embeds(data, prev, s, w);
    }
}

//  ============================================================
//  Part V: Translation of base word at shifted level
//  ============================================================

///  translate_word_at(data, ε, base_level) = ε for any base_level.
proof fn lemma_translate_empty_at(data: HNNData, base_level: int)
    ensures
        translate_word_at(data, empty_word(), base_level) =~= empty_word(),
{}

///  **Britton's Lemma (Unconditional, Lyndon-Schupp Ch. IV):**
///  If w is a base word and w ≡ ε in the HNN extension G*, then w ≡ ε in G.
///
///  No additional assumptions beyond hnn_data_valid and hnn_associations_isomorphic.
///  The tower textbook prerequisites are derived from hnn_associations_isomorphic,
///  and the derivation levels are handled by shifting to a non-negative base level.
pub proof fn britton_lemma_unconditional(
    data: HNNData, w: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
    let hp = hnn_presentation(data);
    let ng = data.base.num_generators;

    //  Get the derivation
    let d: Derivation = choose|d: Derivation|
        derivation_valid(hp, d, w, empty_word());

    //  Compute shift amount from derivation bounds
    let min_adj = derivation_min_adj_level(data, d.steps, w);
    let max_lev = derivation_max_step_level(data, d.steps, w);
    //  base_level >= -min_adj ensures shifted levels are valid
    let base_level: nat = if min_adj >= 0 { 0 } else { (-min_adj) as nat };
    //  m >= max_lev + base_level and m >= base_level (since max_lev >= 0 for base word derivations)
    //  Use base_level + max_lev.abs() + 1 as a safe upper bound
    let max_lev_abs: nat = if max_lev >= 0 { max_lev as nat } else { (-max_lev) as nat };
    let m: nat = (base_level + max_lev_abs + 1) as nat;

    //  base_level <= m (since m = base_level + max_lev_abs + 1 > base_level)
    assert(base_level <= m);
    //  m >= max_lev + base_level (since m = base_level + |max_lev| + 1 >= base_level + max_lev)
    assert(m as int >= max_lev + base_level as int);

    //  word_valid(w, hp.num_generators) — weaken from ng to ng+1
    assert(word_valid(w, hp.num_generators)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies symbol_valid(#[trigger] w[k], hp.num_generators)
        by {}
    }

    //  Step 1: Levels are OK with the chosen base_level
    lemma_derivation_levels_ok_from_bounds(data, m, base_level as int, d.steps, w);

    //  Step 2: Translate derivation to tower equivalence
    lemma_hnn_derivation_to_tower_equiv(data, m, base_level as int, d.steps, w, empty_word());

    //  Step 3: translate_at(w, base_level) = shift_word(w, base_level * ng)
    lemma_translate_base_word_at(data, w, base_level);
    //  Step 3b: translate_at(ε, base_level) = ε
    lemma_translate_empty_at(data, base_level as int);

    //  Step 4: Tower textbook chain from hnn_associations_isomorphic
    lemma_tower_textbook_chain_from_hnn_iso(data, m);

    //  Step 5: Copy-s tower embedding → w ≡ ε in base
    lemma_copy_s_embeds(data, m, base_level, w);
}

} //  verus!
