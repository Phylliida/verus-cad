//  Britton's Lemma — Fully verified formalization (0 errors, 0 assumes)
//  Following Lyndon-Schupp Chapter IV: tower construction + AFP injectivity

//  Foundation
#[cfg(verus_keep_ghost)]
pub mod symbol;
#[cfg(verus_keep_ghost)]
pub mod word;
#[cfg(verus_keep_ghost)]
pub mod reduction;

//  Group presentations and equivalence
#[cfg(verus_keep_ghost)]
pub mod presentation;
#[cfg(verus_keep_ghost)]
pub mod presentation_lemmas;

//  Algebraic structures
#[cfg(verus_keep_ghost)]
pub mod quotient;
#[cfg(verus_keep_ghost)]
pub mod free_product;
#[cfg(verus_keep_ghost)]
pub mod amalgamated_free_product;
#[cfg(verus_keep_ghost)]
pub mod hnn;
#[cfg(verus_keep_ghost)]
pub mod homomorphism;
#[cfg(verus_keep_ghost)]
pub mod benign;

//  Supporting infrastructure
#[cfg(verus_keep_ghost)]
pub mod shortlex;
#[cfg(verus_keep_ghost)]
pub mod todd_coxeter;

//  Normal form theorems
#[cfg(verus_keep_ghost)]
pub mod normal_form_free_product;
#[cfg(verus_keep_ghost)]
pub mod normal_form_amalgamated;
#[cfg(verus_keep_ghost)]
pub mod normal_form_afp_textbook;

//  Tower construction and Britton's lemma
#[cfg(verus_keep_ghost)]
pub mod tower;
#[cfg(verus_keep_ghost)]
pub mod britton_via_tower;
