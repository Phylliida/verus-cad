// Tower construction for Britton's lemma.
//
// Defines the iterated amalgamated free product T_n = G_0 *_A G_1 *_A ... *_A G_n
// and proves that G = G_0 embeds in T_n (conditional on Cayley table existence).
//
// The tower is built recursively:
//   tower(data, 0) = data.base
//   tower(data, n+1) = AFP(tower(data, n), data.base, identifications at junction n↔n+1)
//
// Copy k uses generators k*ng .. (k+1)*ng - 1 where ng = base.num_generators.
// Junction k↔k+1 identifies a_i in copy k with b_i in copy k+1.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::normal_form_amalgamated::*;
use crate::hnn::*;

verus! {

// ============================================================
// Part A: Tower definitions
// ============================================================

/// The AFP data at tower junction k: tower(k) *_A base.
///   p1 = tower(k)
///   p2 = base
///   identifications[i] = (shift(a_i, k*ng), b_i)
pub open spec fn tower_afp_data(data: HNNData, k: nat) -> AmalgamatedData
    decreases k, 1nat,
{
    let ng = data.base.num_generators;
    AmalgamatedData {
        p1: tower_presentation(data, k),
        p2: data.base,
        identifications: Seq::new(
            data.associations.len(),
            |i: int| (
                shift_word(data.associations[i].0, k * ng),
                data.associations[i].1,
            ),
        ),
    }
}

/// Tower presentation: (n+1) copies of G, glued by identification relators.
///   tower(data, 0) = data.base
///   tower(data, n+1) = amalgamated_free_product(tower_afp_data(data, n))
pub open spec fn tower_presentation(data: HNNData, n: nat) -> Presentation
    decreases n, 0nat,
{
    if n == 0 {
        data.base
    } else {
        amalgamated_free_product(tower_afp_data(data, (n - 1) as nat))
    }
}

/// Shift a word to copy k in the tower.
pub open spec fn word_in_copy(w: Word, ng: nat, k: nat) -> Word {
    shift_word(w, k * ng)
}

// ============================================================
// Part B: Tower structural lemmas
// ============================================================

/// Tower has (n+1)*ng generators.
pub proof fn lemma_tower_num_generators(data: HNNData, n: nat)
    requires
        hnn_data_valid(data),
    ensures
        tower_presentation(data, n).num_generators == (n + 1) * data.base.num_generators,
    decreases n,
{
    let ng = data.base.num_generators;
    if n == 0 {
        assert(tower_presentation(data, 0).num_generators == ng);
        assert(ng == 1 * ng);
    } else {
        let prev = (n - 1) as nat;
        lemma_tower_num_generators(data, prev);
        let afp_data = tower_afp_data(data, prev);
        crate::amalgamated_free_product::lemma_add_relators_num_generators(
            free_product(afp_data.p1, afp_data.p2),
            amalgamation_relators(afp_data),
        );
        assert(free_product(afp_data.p1, afp_data.p2).num_generators
            == afp_data.p1.num_generators + afp_data.p2.num_generators);
        assert(afp_data.p1.num_generators == n * ng);
        assert(afp_data.p2.num_generators == ng);
        assert(tower_presentation(data, n).num_generators == n * ng + ng);
        assert(n * ng + ng == (n + 1) * ng) by (nonlinear_arith);
    }
}

/// word_valid monotonicity: valid for m implies valid for any m' >= m.
proof fn lemma_word_valid_weaken(w: Word, m: nat, m_prime: nat)
    requires
        word_valid(w, m),
        m <= m_prime,
    ensures
        word_valid(w, m_prime),
{
    assert forall|k: int| 0 <= k < w.len()
        implies symbol_valid(w[k], m_prime)
    by {
        assert(symbol_valid(w[k], m));
        match w[k] {
            Symbol::Gen(i) => {}
            Symbol::Inv(i) => {}
        }
    }
}

/// Tower presentation is valid at every level.
pub proof fn lemma_tower_valid(data: HNNData, n: nat)
    requires
        hnn_data_valid(data),
    ensures
        presentation_valid(tower_presentation(data, n)),
    decreases n, 0nat,
{
    if n == 0 {
        reveal(presentation_valid);
    } else {
        let prev = (n - 1) as nat;
        lemma_tower_afp_data_valid(data, prev);
        lemma_amalgamated_valid(tower_afp_data(data, prev));
    }
}

/// The tower AFP data at level k has valid amalgamated data.
pub proof fn lemma_tower_afp_data_valid(data: HNNData, k: nat)
    requires
        hnn_data_valid(data),
    ensures
        amalgamated_data_valid(tower_afp_data(data, k)),
    decreases k, 1nat,
{
    let ng = data.base.num_generators;
    let afp_data = tower_afp_data(data, k);

    reveal(presentation_valid);
    assert(presentation_valid(data.base));

    lemma_tower_valid(data, k);
    lemma_tower_num_generators(data, k);

    assert forall|i: int| 0 <= i < afp_data.identifications.len()
        implies ({
            &&& word_valid(afp_data.identifications[i].0, afp_data.p1.num_generators)
            &&& word_valid(afp_data.identifications[i].1, afp_data.p2.num_generators)
        })
    by {
        let a_i = data.associations[i].0;
        let b_i = data.associations[i].1;
        let u_i = shift_word(a_i, k * ng);
        assert(afp_data.identifications[i] == (u_i, b_i));
        assert(word_valid(a_i, ng));
        assert(word_valid(b_i, ng));
        // shift(a_i, k*ng) is word_valid for (k+1)*ng = tower(k).num_generators
        assert(afp_data.p1.num_generators == (k + 1) * ng);
        assert forall|j: int| 0 <= j < u_i.len()
            implies symbol_valid(u_i[j], (k + 1) * ng)
        by {
            assert(symbol_valid(a_i[j], ng));
            match a_i[j] {
                Symbol::Gen(idx) => {
                    assert(u_i[j] == Symbol::Gen((idx + k * ng) as nat));
                    assert(idx + k * ng < (k + 1) * ng) by (nonlinear_arith)
                        requires idx < ng;
                }
                Symbol::Inv(idx) => {
                    assert(u_i[j] == Symbol::Inv((idx + k * ng) as nat));
                    assert(idx + k * ng < (k + 1) * ng) by (nonlinear_arith)
                        requires idx < ng;
                }
            }
        }
    }
}

// ============================================================
// Part C: Textbook tower embedding (uses one-shot AFP injectivity)
// ============================================================

/// Textbook prerequisites at tower level k:
/// - identifications_isomorphic: the identification map is an isomorphism
/// - action_preserves_canonical: the van der Waerden action preserves canonical states
/// (identity state canonicality is now proved from amalgamated_data_valid via lemma_identity_state_canonical)
pub open spec fn tower_textbook_prereqs_at(data: HNNData, k: nat) -> bool {
    let afp_data = tower_afp_data(data, k);
    &&& crate::normal_form_amalgamated::identifications_isomorphic(afp_data)
    &&& crate::normal_form_afp_textbook::action_preserves_canonical(afp_data)
}

/// Textbook prerequisites hold at all tower levels 0..n-1.
pub open spec fn tower_textbook_chain(data: HNNData, n: nat) -> bool {
    forall|k: nat| k < n ==> #[trigger] tower_textbook_prereqs_at(data, k)
}

/// Textbook tower embedding: G_0 embeds in tower(n) via one-shot AFP injectivity.
/// Same structure as lemma_g0_embeds_in_tower but with simpler prerequisites.
pub proof fn lemma_g0_embeds_in_tower_textbook(
    data: HNNData, n: nat, w: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(tower_presentation(data, n), w, empty_word()),
        tower_textbook_chain(data, n),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
    decreases n,
{
    if n == 0 {
    } else {
        let prev = (n - 1) as nat;
        let ng = data.base.num_generators;
        let afp_data = tower_afp_data(data, prev);

        lemma_tower_num_generators(data, prev);
        assert(ng <= n * ng) by (nonlinear_arith) requires n >= 1;
        lemma_word_valid_weaken(w, ng, n * ng);

        lemma_tower_valid(data, prev);
        lemma_tower_afp_data_valid(data, prev);

        // Textbook AFP injectivity at level prev
        assert(tower_textbook_prereqs_at(data, prev));
        crate::normal_form_afp_textbook::lemma_afp_injectivity(afp_data, w);

        // IH
        assert(tower_textbook_chain(data, prev)) by {
            assert forall|k: nat| k < prev
                implies #[trigger] tower_textbook_prereqs_at(data, k)
            by { assert(k < n); }
        }
        lemma_g0_embeds_in_tower_textbook(data, prev, w);
    }
}

} // verus!
