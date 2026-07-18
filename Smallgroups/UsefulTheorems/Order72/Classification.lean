/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.Residual
import Smallgroups.UsefulTheorems.Order72.H8xP9

/-!
## Open assumption

The three branches of the order-`72` classification that are already machine-checked are
the Sylow-`3`-normal branch (`order72Sylow3NormalSolvedAllCases`), the Sylow-`2`-normal
branch (`order72Sylow2NormalRepCases`), and the reduction of the residual branch to its
kernel/image analysis (`order72ResidualKernelCases`).  The only remaining step is turning
that kernel/image endpoint into the four explicit residual representatives
(`order72ResidualRepCases`).  That conversion is the deep group-theoretic argument
documented in `Residual.lean`; until it is formalised it is assumed by the following
axiom, which is the single open assumption of this classification assembly. -/

axiom order72_residual_kernel_cases_to_repCases {G : Type} [Group G] [Finite G]
    (hG : Nat.card G = 72) (hker : Smallgroups.UsefulTheorems.order72ResidualKernelCases G) :
    Smallgroups.UsefulTheorems.order72ResidualRepCases G

/-!
# The groups of order 72

This file assembles the three completed branches of the order-`72` classification into
the full list of representatives `order72_reps : Fin 50 → Type`:

* **Sylow-`3`-normal branch** (`n₃ = 1`, `order72Sylow3NormalSolvedAllCases`): the
  `C9 ⋊ H` and `E9 ⋊ H` semidirect products for `H` one of the five order-`8` groups,
  together with the direct products `C9 × H` and `E9 × H`.  Note that the `C9 ⋊ H2`
  cell contributes only **two** nontrivial classes, since the product inversion
  `order72_C9_H2_prodInv` is isomorphic to the second-factor inversion
  `order72_C9_H2_sndInv` (`order72_C9_H2_prodInv_iso_sndInv`); the duplicate is
  therefore not listed separately.
* **Sylow-`2`-normal branch** (`n₂ = 1`, `order72Sylow2NormalRepCases`): the `H × K`
  direct products and the four nontrivial `Q8`/`E8` actions.
* **Residual branch** (`n₃ = 4 ∧ n₂ ≠ 1`, `order72ResidualRepCases`): the non-split
  `C₃.S₄`, `C₃ × S₄`, `C₃ ⋊[sign] S₄`, and `S₃ × A₄`.

The GAP SmallGroups library lists exactly `50` isomorphism classes of order `72`.  The
Sylow-`3`-normal branch contributes `42` (its `10` direct products are shared with the
Sylow-`2`-normal branch), the Sylow-`2`-normal branch contributes `14`, and the residual
branch contributes `4`; the shared direct products are listed once, giving
`42 + 14 − 10 + 4 = 50`.

This file provides the exhaustiveness statement `order72_complete` (every group
of order `72` is isomorphic to one of the fifty listed representatives) and the
cardinality statement `order72_reps_card`.  Distinctness (`order72_reps_pairwise`) and
the final `IsClassif` instance are proved separately. -/

namespace Smallgroups.UsefulTheorems

open Sylow P3Group

variable {G : Type*} [Group G]

/-! ### The fifty representatives -/

/-- The representatives of the `50` isomorphism classes of groups of order `72`:
indices `0–9` are the direct products, `10–16` the nontrivial `C9 ⋊ H` semidirect
products, `17–41` the nontrivial `E9 ⋊ H` semidirect products, `42–45` the nontrivial
actions on the normal Sylow `2`-subgroup, and `46–49` the four residual groups. -/
noncomputable abbrev order72_reps (n : Fin 50) : Type :=
  match n with
  | ⟨0, _⟩ => CyclicRep 9 × Multiplicative (ZMod 8)
  | ⟨1, _⟩ => CyclicRep 9 × H2
  | ⟨2, _⟩ => CyclicRep 9 × E8
  | ⟨3, _⟩ => CyclicRep 9 × DihedralGroup 4
  | ⟨4, _⟩ => CyclicRep 9 × QuaternionGroup 2
  | ⟨5, _⟩ => ElemAbelianRep 3 × Multiplicative (ZMod 8)
  | ⟨6, _⟩ => ElemAbelianRep 3 × H2
  | ⟨7, _⟩ => ElemAbelianRep 3 × E8
  | ⟨8, _⟩ => ElemAbelianRep 3 × DihedralGroup 4
  | ⟨9, _⟩ => ElemAbelianRep 3 × QuaternionGroup 2
  | ⟨10, _⟩ => order72_C9_C8_inv
  | ⟨11, _⟩ => order72_C9_H2_fstInv
  | ⟨12, _⟩ => order72_C9_H2_sndInv
  | ⟨13, _⟩ => order72_C9_E8_inv100
  | ⟨14, _⟩ => order72_C9_Q8_invA
  | ⟨15, _⟩ => order72_C9_D4_invRot
  | ⟨16, _⟩ => order72_C9_D4_invRef
  | ⟨17, _⟩ => order72_E9_C8_neg
  | ⟨18, _⟩ => order72_E9_C8_reflect
  | ⟨19, _⟩ => order72_E9_C8_order4
  | ⟨20, _⟩ => order72_E9_C8_order8
  | ⟨21, _⟩ => order72_E9_H2_fstNeg
  | ⟨22, _⟩ => order72_E9_H2_sndNeg
  | ⟨23, _⟩ => order72_E9_H2_fstReflect
  | ⟨24, _⟩ => order72_E9_H2_sndReflect
  | ⟨25, _⟩ => order72_E9_H2_v4NegReflect
  | ⟨26, _⟩ => order72_E9_H2_v4ReflectNeg
  | ⟨27, _⟩ => order72_E9_H2_order4
  | ⟨28, _⟩ => order72_E9_E8_neg100
    | ⟨29, _⟩ => order72_E9_E8_reflect100
  | ⟨30, _⟩ => order72_E9_E8_v4
  | ⟨31, _⟩ => order72_E9_Q8_negI
  | ⟨32, _⟩ => order72_E9_Q8_reflectI
  | ⟨33, _⟩ => order72_E9_Q8_v4
  | ⟨34, _⟩ => order72_E9_Q8_faithful
  | ⟨35, _⟩ => order72_E9_D4_sNeg
  | ⟨36, _⟩ => order72_E9_D4_sReflect
  | ⟨37, _⟩ => order72_E9_D4_rNeg
  | ⟨38, _⟩ => order72_E9_D4_rReflect
  | ⟨39, _⟩ => order72_E9_D4_v4NegReflect
  | ⟨40, _⟩ => order72_E9_D4_v4ReflectNeg
  | ⟨41, _⟩ => order72_E9_D4_faithful
  | ⟨42, _⟩ => order72_Q8_C9_cyc
  | ⟨43, _⟩ => order72_Q8_E9_cyc
  | ⟨44, _⟩ => order72_E8_C9_rot
  | ⟨45, _⟩ => order72_E8_E9_rot
  | ⟨46, _⟩ => order72ResidualRep 0
  | ⟨47, _⟩ => order72ResidualRep 1
  | ⟨48, _⟩ => order72ResidualRep 2
  | ⟨49, _⟩ => order72ResidualRep 3
  | ⟨n + 50, h⟩ => by omega

/-- Swaps the factors of a direct-product isomorphism: given Nonempty (G ≃* (H × K))
returns Nonempty (G ≃* (K × H)). -/
@[reducible]
def order72_swapProd {H K : Type*} [Group H] [Group K]
    (h : Nonempty (G ≃* H × K)) : Nonempty (G ≃* K × H) :=
  let ⟨e⟩ := h
  ⟨e.trans MulEquiv.prodComm⟩

noncomputable instance order72_reps_group (n : Fin 50) : Group (order72_reps n) :=
  match n with
  | ⟨0, _⟩ => inferInstance
  | ⟨1, _⟩ => inferInstance
  | ⟨2, _⟩ => inferInstance
  | ⟨3, _⟩ => inferInstance
  | ⟨4, _⟩ => inferInstance
  | ⟨5, _⟩ => inferInstance
  | ⟨6, _⟩ => inferInstance
  | ⟨7, _⟩ => inferInstance
  | ⟨8, _⟩ => inferInstance
  | ⟨9, _⟩ => inferInstance
  | ⟨10, _⟩ => inferInstance
  | ⟨11, _⟩ => inferInstance
  | ⟨12, _⟩ => inferInstance
  | ⟨13, _⟩ => inferInstance
  | ⟨14, _⟩ => inferInstance
  | ⟨15, _⟩ => inferInstance
  | ⟨16, _⟩ => inferInstance
  | ⟨17, _⟩ => inferInstance
  | ⟨18, _⟩ => inferInstance
  | ⟨19, _⟩ => inferInstance
  | ⟨20, _⟩ => inferInstance
  | ⟨21, _⟩ => inferInstance
  | ⟨22, _⟩ => inferInstance
  | ⟨23, _⟩ => inferInstance
  | ⟨24, _⟩ => inferInstance
  | ⟨25, _⟩ => inferInstance
  | ⟨26, _⟩ => inferInstance
  | ⟨27, _⟩ => inferInstance
  | ⟨28, _⟩ => inferInstance
  | ⟨29, _⟩ => inferInstance
  | ⟨30, _⟩ => inferInstance
  | ⟨31, _⟩ => inferInstance
  | ⟨32, _⟩ => inferInstance
  | ⟨33, _⟩ => inferInstance
  | ⟨34, _⟩ => inferInstance
  | ⟨35, _⟩ => inferInstance
  | ⟨36, _⟩ => inferInstance
  | ⟨37, _⟩ => inferInstance
  | ⟨38, _⟩ => inferInstance
  | ⟨39, _⟩ => inferInstance
  | ⟨40, _⟩ => inferInstance
  | ⟨41, _⟩ => inferInstance
  | ⟨42, _⟩ => inferInstance
  | ⟨43, _⟩ => inferInstance
  | ⟨44, _⟩ => inferInstance
    | ⟨45, _⟩ => inferInstance
  | ⟨46, _⟩ => inferInstance
  | ⟨47, _⟩ => inferInstance
  | ⟨48, _⟩ => inferInstance
  | ⟨49, _⟩ => inferInstance
  | ⟨n + 50, h⟩ => by omega

/-! ### Distinctness branch bookkeeping -/

/-- Bookkeeping branches used to assemble distinctness by `PairwiseNonMulEquiv.sigma`. -/
inductive Order72Branch
  | direct
  | c9
  | e9
  | sylow2
  | residual
  deriving DecidableEq

/-- The index type of each distinctness branch. -/
abbrev order72_branch_index : Order72Branch → Type
  | .direct => Fin 10
  | .c9 => Fin 7
  | .e9 => Fin 25
  | .sylow2 => Fin 4
  | .residual => Fin 4

/-- The `Fin 50` index represented by a branch index. -/
def order72_branch_to_fin : (b : Order72Branch) → order72_branch_index b → Fin 50
  | .direct, i => ⟨i.val, by omega⟩
  | .c9, i => ⟨10 + i.val, by omega⟩
  | .e9, i => ⟨17 + i.val, by omega⟩
  | .sylow2, i => ⟨42 + i.val, by omega⟩
  | .residual, i => ⟨46 + i.val, by omega⟩

/-- The same fifty representatives, grouped by the distinctness proof branches. -/
noncomputable abbrev order72_branch_reps (b : Order72Branch) (i : order72_branch_index b) :
    Type :=
  order72_reps (order72_branch_to_fin b i)

/-- Flattened branch representatives. -/
noncomputable abbrev order72_sigma_reps :
    (Σ b : Order72Branch, order72_branch_index b) → Type :=
  fun s => order72_branch_reps s.1 s.2

noncomputable instance order72_branch_reps_group :
    (b : Order72Branch) → (i : order72_branch_index b) → Group (order72_branch_reps b i)
  | b, i => order72_reps_group (order72_branch_to_fin b i)

noncomputable instance order72_sigma_reps_group
    (s : Σ b : Order72Branch, order72_branch_index b) : Group (order72_sigma_reps s) :=
  order72_branch_reps_group s.1 s.2

/-- The bookkeeping index from the original `Fin 50` list to the grouped `Σ` list. -/
def order72_index : Fin 50 → Σ b : Order72Branch, order72_branch_index b
  | 0 => ⟨.direct, 0⟩
  | 1 => ⟨.direct, 1⟩
  | 2 => ⟨.direct, 2⟩
  | 3 => ⟨.direct, 3⟩
  | 4 => ⟨.direct, 4⟩
  | 5 => ⟨.direct, 5⟩
  | 6 => ⟨.direct, 6⟩
  | 7 => ⟨.direct, 7⟩
  | 8 => ⟨.direct, 8⟩
  | 9 => ⟨.direct, 9⟩
  | 10 => ⟨.c9, 0⟩
  | 11 => ⟨.c9, 1⟩
  | 12 => ⟨.c9, 2⟩
  | 13 => ⟨.c9, 3⟩
  | 14 => ⟨.c9, 4⟩
  | 15 => ⟨.c9, 5⟩
  | 16 => ⟨.c9, 6⟩
  | 17 => ⟨.e9, 0⟩
  | 18 => ⟨.e9, 1⟩
  | 19 => ⟨.e9, 2⟩
  | 20 => ⟨.e9, 3⟩
  | 21 => ⟨.e9, 4⟩
  | 22 => ⟨.e9, 5⟩
  | 23 => ⟨.e9, 6⟩
  | 24 => ⟨.e9, 7⟩
  | 25 => ⟨.e9, 8⟩
  | 26 => ⟨.e9, 9⟩
  | 27 => ⟨.e9, 10⟩
  | 28 => ⟨.e9, 11⟩
  | 29 => ⟨.e9, 12⟩
  | 30 => ⟨.e9, 13⟩
  | 31 => ⟨.e9, 14⟩
  | 32 => ⟨.e9, 15⟩
  | 33 => ⟨.e9, 16⟩
  | 34 => ⟨.e9, 17⟩
  | 35 => ⟨.e9, 18⟩
  | 36 => ⟨.e9, 19⟩
  | 37 => ⟨.e9, 20⟩
  | 38 => ⟨.e9, 21⟩
  | 39 => ⟨.e9, 22⟩
  | 40 => ⟨.e9, 23⟩
  | 41 => ⟨.e9, 24⟩
  | 42 => ⟨.sylow2, 0⟩
  | 43 => ⟨.sylow2, 1⟩
  | 44 => ⟨.sylow2, 2⟩
  | 45 => ⟨.sylow2, 3⟩
  | 46 => ⟨.residual, 0⟩
  | 47 => ⟨.residual, 1⟩
  | 48 => ⟨.residual, 2⟩
  | 49 => ⟨.residual, 3⟩
  | ⟨k + 50, h⟩ => by omega

set_option maxHeartbeats 2000000 in
-- Finite 50-by-50 case split checking that the branch bookkeeping index is injective.
theorem order72_index_injective : Function.Injective order72_index := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [order72_index] at h ⊢

theorem order72_reps_eq_sigma_reps (n : Fin 50) :
    order72_reps n = order72_sigma_reps (order72_index n) := by
  fin_cases n <;> rfl

theorem order72_branch_to_fin_index (n : Fin 50) :
    order72_branch_to_fin (order72_index n).1 (order72_index n).2 = n := by
  fin_cases n <;> rfl

theorem order72_reps_to_sigma_iso {i j : Fin 50}
    (hiso : Nonempty (order72_reps i ≃* order72_reps j)) :
    Nonempty (order72_sigma_reps (order72_index i) ≃*
      order72_sigma_reps (order72_index j)) := by
  obtain ⟨e⟩ := hiso
  change Nonempty
    (order72_reps (order72_branch_to_fin (order72_index i).1 (order72_index i).2) ≃*
      order72_reps (order72_branch_to_fin (order72_index j).1 (order72_index j).2))
  exact ⟨(MulEquiv.cast (order72_branch_to_fin_index i)).trans
    (e.trans (MulEquiv.cast (order72_branch_to_fin_index j).symm))⟩

/-! ### Cardinalities -/

lemma card_order72_C8 : Nat.card (Multiplicative (ZMod 8)) = 8 :=
  Nat.card_eq_fintype_card.trans (by norm_num)

lemma card_order72_D4 : Nat.card (DihedralGroup 4) = 8 := by
  rw [DihedralGroup.nat_card]

lemma fintype_card_order72_Q8 : Fintype.card (QuaternionGroup 2) = 8 := by
  rw [← Nat.card_eq_fintype_card]; exact card_order72_Q8

lemma fintype_card_order72_D4 : Fintype.card (DihedralGroup 4) = 8 := by
  rw [← Nat.card_eq_fintype_card]; exact card_order72_D4

theorem order72_reps_card (m : Fin 50) : Nat.card (order72_reps m) = 72 := by
  fin_cases m
  all_goals (dsimp; simp only [order72_reps]; first
    | exact card_order72ResidualRep (0 : Fin 4)
    | exact card_order72ResidualRep (1 : Fin 4)
    | exact card_order72ResidualRep (2 : Fin 4)
    | exact card_order72ResidualRep (3 : Fin 4)
    | exact card_order72_Q8_C9_cyc
    | exact card_order72_Q8_E9_cyc
    | exact card_order72_E8_C9_rot
    | exact card_order72_E8_E9_rot
    | (rw [SemidirectProduct.card]; norm_num [card_order72_C9, card_order72_E9,
        card_order72_H2, card_order72_E8, card_order72_Q8, card_order72_C8, card_order72_D4,
        fintype_card_order72_Q8, fintype_card_order72_D4])
    | (rw [Nat.card_prod]; norm_num [card_order72_C9, card_order72_E9,
        card_order72_H2, card_order72_E8, card_order72_Q8, card_order72_C8, card_order72_D4,
        fintype_card_order72_Q8, fintype_card_order72_D4]))

/-! ### Exhaustiveness: mapping the branch disjunctions onto the fifty representatives -/

private theorem order72_exists_rep_of_c9_cases {G : Type} [Group G]
    (h : order72Sylow3NormalSolvedC9Cases G) :
    ∃ n : Fin 50, Nonempty (G ≃* order72_reps n) := by
  rcases h with hC9C8 | hC9C8inv | hC9H2 | hC9H2f | hC9H2s | hC9H2p
  · exact ⟨0, hC9C8⟩
  · exact ⟨10, hC9C8inv⟩
  · exact ⟨1, hC9H2⟩
  · exact ⟨11, hC9H2f⟩
  · exact ⟨12, hC9H2s⟩
  · -- The product inversion is isomorphic to the second-factor inversion
    -- (`order72_C9_H2_prodInv_iso_sndInv`), so it maps to the same representative.
    obtain ⟨f⟩ := order72_C9_H2_prodInv_iso_sndInv
    exact ⟨12, hC9H2p.map (·.trans f)⟩

private theorem order72_exists_rep_of_c9_all_cases {G : Type} [Group G]
    (h : order72Sylow3NormalSolvedC9AllCases G) :
    ∃ n : Fin 50, Nonempty (G ≃* order72_reps n) := by
  rcases h with hprev | hC9E8 | hC9E8inv | hC9Q8 | hC9Q8inv | hC9D4 | hC9D4rot | hC9D4ref
  · exact order72_exists_rep_of_c9_cases hprev
  · exact ⟨2, hC9E8⟩
  · exact ⟨13, hC9E8inv⟩
  · exact ⟨4, hC9Q8⟩
  · exact ⟨14, hC9Q8inv⟩
  · exact ⟨3, hC9D4⟩
  · exact ⟨15, hC9D4rot⟩
  · exact ⟨16, hC9D4ref⟩

private theorem order72_exists_rep_of_e9c8_cases {G : Type} [Group G]
    (h : order72Sylow3NormalSolvedC9AllE9C8Cases G) :
    ∃ n : Fin 50, Nonempty (G ≃* order72_reps n) := by
  rcases h with hprev | hE9C8 | hE9C8neg | hE9C8ref | hE9C8o4 | hE9C8o8
  · exact order72_exists_rep_of_c9_all_cases hprev
  · exact ⟨5, hE9C8⟩
  · exact ⟨17, hE9C8neg⟩
  · exact ⟨18, hE9C8ref⟩
  · exact ⟨19, hE9C8o4⟩
  · exact ⟨20, hE9C8o8⟩

private theorem order72_exists_rep_of_h2_cases {G : Type} [Group G]
    (h : order72Sylow3NormalSolvedC9AllE9C8H2Cases G) :
    ∃ n : Fin 50, Nonempty (G ≃* order72_reps n) := by
  rcases h with hprev | hE9H2 | hfN | hsN | hfR | hsR | hv4NR | hv4RN | ho4
  · exact order72_exists_rep_of_e9c8_cases hprev
  · exact ⟨6, hE9H2⟩
  · exact ⟨21, hfN⟩
  · exact ⟨22, hsN⟩
  · exact ⟨23, hfR⟩
  · exact ⟨24, hsR⟩
  · exact ⟨25, hv4NR⟩
  · exact ⟨26, hv4RN⟩
  · exact ⟨27, ho4⟩

private theorem order72_exists_rep_of_e8_cases {G : Type} [Group G]
    (h : order72Sylow3NormalSolvedC9AllE9C8H2E8Cases G) :
    ∃ n : Fin 50, Nonempty (G ≃* order72_reps n) := by
  rcases h with hprev | hE9E8 | hn | hr | hv4
  · exact order72_exists_rep_of_h2_cases hprev
  · exact ⟨7, hE9E8⟩
  · exact ⟨28, hn⟩
  · exact ⟨29, hr⟩
  · exact ⟨30, hv4⟩

private theorem order72_exists_rep_of_q8_cases {G : Type} [Group G]
    (h : order72Sylow3NormalSolvedC9AllE9C8H2E8Q8Cases G) :
    ∃ n : Fin 50, Nonempty (G ≃* order72_reps n) := by
  rcases h with hprev | hE9Q8 | hnI | hrI | hv4 | hf
  · exact order72_exists_rep_of_e8_cases hprev
  · exact ⟨9, hE9Q8⟩
  · exact ⟨31, hnI⟩
  · exact ⟨32, hrI⟩
  · exact ⟨33, hv4⟩
  · exact ⟨34, hf⟩

private theorem order72_exists_rep_of_solved_all_cases {G : Type} [Group G]
    (h : order72Sylow3NormalSolvedAllCases G) :
    ∃ n : Fin 50, Nonempty (G ≃* order72_reps n) := by
  rcases h with hprev | hE9D4 | hsN | hsR | hrN | hrR | hv4NR | hv4RN | hf
  · exact order72_exists_rep_of_q8_cases hprev
  · exact ⟨8, hE9D4⟩
  · exact ⟨35, hsN⟩
  · exact ⟨36, hsR⟩
  · exact ⟨37, hrN⟩
  · exact ⟨38, hrR⟩
  · exact ⟨39, hv4NR⟩
  · exact ⟨40, hv4RN⟩
  · exact ⟨41, hf⟩

private theorem order72_exists_rep_of_sylow2_cases {G : Type} [Group G]
    (h : order72Sylow2NormalRepCases G) :
    ∃ n : Fin 50, Nonempty (G ≃* order72_reps n) := by
  rcases h with hC8C9 | hC8E9 | hH2C9 | hH2E9 | hE8C9 | hE8E9 | hD4C9 | hD4E9 |
    hQ8C9 | hQ8E9 | hQ8c9 | hQ8e9 | hE8c9 | hE8e9
  · exact ⟨0, order72_swapProd hC8C9⟩
  · exact ⟨5, order72_swapProd hC8E9⟩
  · exact ⟨1, order72_swapProd hH2C9⟩
  · exact ⟨6, order72_swapProd hH2E9⟩
  · exact ⟨2, order72_swapProd hE8C9⟩
  · exact ⟨7, order72_swapProd hE8E9⟩
  · exact ⟨3, order72_swapProd hD4C9⟩
  · exact ⟨8, order72_swapProd hD4E9⟩
  · exact ⟨4, order72_swapProd hQ8C9⟩
  · exact ⟨9, order72_swapProd hQ8E9⟩
  · exact ⟨42, hQ8c9⟩
  · exact ⟨43, hQ8e9⟩
  · exact ⟨44, by simp only [order72_reps]; exact hE8c9⟩
  · exact ⟨45, by simp only [order72_reps]; exact hE8e9⟩

/-- Every group of order `72` is isomorphic to one of the fifty representatives. -/
theorem order72_complete (G : Type) [Group G] (hG : Nat.card G = 72) :
    ∃ n : Fin 50, Nonempty (G ≃* order72_reps n) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  rcases order72_rep_cases_of_residual_kernel_cases_done
      (fun hG' hres' => order72_residual_kernel_cases_to_repCases hG' hres') hG with
    h3 | h2 | hres
  · exact order72_exists_rep_of_solved_all_cases h3
  · exact order72_exists_rep_of_sylow2_cases h2
  · rcases hres with hC3S4 | hC3xS4 | hC3sS4 | hS3xA4
    · exact ⟨46, by simp only [order72_reps, order72ResidualRep, order72_res_C3S4]; exact hC3S4⟩
    · exact ⟨47, by simp only [order72_reps, order72ResidualRep, order72_res_C3xS4]; exact hC3xS4⟩
    · exact ⟨48, by simp only [order72_reps, order72ResidualRep, order72_res_C3sS4]; exact hC3sS4⟩
    · exact ⟨49, by simp only [order72_reps, order72ResidualRep, order72_res_S3xA4]; exact hS3xA4⟩

/-! ### Counting -/

theorem order72_classCount : Nat.card (Fin 50) = 50 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### Distinctness and `IsClassif` packaging -/

/-- Number of elements satisfying `x ^ n = 1`. -/
noncomputable def order72_pow_eq_one_card (H : Type*) [Group H] (n : ℕ) : ℕ :=
  Nat.card {x : H // x ^ n = 1}

/-- The `x ^ n = 1` count is invariant under multiplicative equivalence. -/
noncomputable def order72_powEqOneEquivOfMulEquiv {H K : Type*} [Group H] [Group K]
    (n : ℕ) (e : H ≃* K) : {x : H // x ^ n = 1} ≃ {x : K // x ^ n = 1} where
  toFun x := ⟨e x.1, by rw [← map_pow, x.2, map_one]⟩
  invFun x := ⟨e.symm x.1, by
    rw [← map_pow]
    exact e.injective (by simp [x.2])⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp

theorem order72_pow_eq_one_card_eq_of_mulEquiv {H K : Type*} [Group H] [Group K]
    (n : ℕ) (e : H ≃* K) :
    order72_pow_eq_one_card H n = order72_pow_eq_one_card K n :=
  Nat.card_congr (order72_powEqOneEquivOfMulEquiv n e)

/-- The invariant tuple type used for the order-72 distinctness bookkeeping. -/
abbrev Order72Invariant :=
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat

/-- A finite tuple of elementary isomorphism invariants used to separate the representatives. -/
noncomputable def order72_reps_invariant (i : Fin 50) : Order72Invariant :=
  (Nat.card (Subgroup.center (order72_reps i)),
    order72_pow_eq_one_card (order72_reps i) 2,
    order72_pow_eq_one_card (order72_reps i) 3,
    order72_pow_eq_one_card (order72_reps i) 4,
    order72_pow_eq_one_card (order72_reps i) 6,
    order72_pow_eq_one_card (order72_reps i) 8,
    order72_pow_eq_one_card (order72_reps i) 9,
    order72_pow_eq_one_card (order72_reps i) 12,
    order72_pow_eq_one_card (order72_reps i) 18,
    order72_pow_eq_one_card (order72_reps i) 24)

theorem order72_reps_invariant_eq_of_mulEquiv {i j : Fin 50}
    (hiso : Nonempty (order72_reps i ≃* order72_reps j)) :
    order72_reps_invariant i = order72_reps_invariant j := by
  obtain ⟨e⟩ := hiso
  simp only [order72_reps_invariant]
  exact Prod.ext (card_center_eq_of_mulEquiv e)
    (Prod.ext (order72_pow_eq_one_card_eq_of_mulEquiv 2 e)
      (Prod.ext (order72_pow_eq_one_card_eq_of_mulEquiv 3 e)
        (Prod.ext (order72_pow_eq_one_card_eq_of_mulEquiv 4 e)
          (Prod.ext (order72_pow_eq_one_card_eq_of_mulEquiv 6 e)
            (Prod.ext (order72_pow_eq_one_card_eq_of_mulEquiv 8 e)
              (Prod.ext (order72_pow_eq_one_card_eq_of_mulEquiv 9 e)
                (Prod.ext (order72_pow_eq_one_card_eq_of_mulEquiv 12 e)
                  (Prod.ext (order72_pow_eq_one_card_eq_of_mulEquiv 18 e)
                    (order72_pow_eq_one_card_eq_of_mulEquiv 24 e)))))))))

theorem order72_reps_pairwise_of_invariant_injective
    (hinj : Function.Injective order72_reps_invariant) :
    PairwiseNonMulEquiv order72_reps := by
  exact PairwiseNonMulEquiv.of_invariant order72_reps_invariant
    (fun _ _ h => order72_reps_invariant_eq_of_mulEquiv h)
    (fun _ _ h _ => hinj h)

theorem order72_reps_pairwise_of_invariant_table
    (tab : Fin 50 → Order72Invariant)
    (hspec : ∀ i, order72_reps_invariant i = tab i)
    (hinj : Function.Injective tab) :
    PairwiseNonMulEquiv order72_reps :=
  order72_reps_pairwise_of_invariant_injective (by
    intro i j h
    apply hinj
    rw [← hspec i, ← hspec j]
    exact h)

noncomputable def order72_branch_invariant (b : Order72Branch)
    (i : order72_branch_index b) : Order72Invariant :=
  order72_reps_invariant (order72_branch_to_fin b i)

theorem order72_branch_invariant_eq_of_mulEquiv {b : Order72Branch}
    {i j : order72_branch_index b}
    (hiso : Nonempty (order72_branch_reps b i ≃* order72_branch_reps b j)) :
    order72_branch_invariant b i = order72_branch_invariant b j := by
  exact order72_reps_invariant_eq_of_mulEquiv hiso

theorem order72_branch_reps_pairwise_of_invariant_injective
    (b : Order72Branch)
    (hinj : Function.Injective (order72_branch_invariant b)) :
    PairwiseNonMulEquiv (order72_branch_reps b) := by
  exact PairwiseNonMulEquiv.of_invariant (order72_branch_invariant b)
    (fun _ _ h => order72_branch_invariant_eq_of_mulEquiv h)
    (fun _ _ h _ => hinj h)

theorem order72_branch_reps_pairwise_of_invariant_table
    (b : Order72Branch)
    (tab : order72_branch_index b → Order72Invariant)
    (hspec : ∀ i, order72_branch_invariant b i = tab i)
    (hinj : Function.Injective tab) :
    PairwiseNonMulEquiv (order72_branch_reps b) :=
  order72_branch_reps_pairwise_of_invariant_injective b (by
    intro i j h
    apply hinj
    rw [← hspec i, ← hspec j]
    exact h)

theorem order72_cross_branch_disjoint_of_invariant_ne
    (hsep : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ i j,
      order72_branch_invariant b₁ i ≠ order72_branch_invariant b₂ j) :
    ∀ b₁ b₂, b₁ ≠ b₂ → ∀ i j,
      ¬ Nonempty (order72_branch_reps b₁ i ≃* order72_branch_reps b₂ j) := by
  intro b₁ b₂ hne i j hiso
  exact hsep b₁ b₂ hne i j (order72_reps_invariant_eq_of_mulEquiv hiso)

theorem order72_cross_branch_disjoint_of_invariant_tables
    (tab : (b : Order72Branch) → order72_branch_index b → Order72Invariant)
    (hspec : ∀ b i, order72_branch_invariant b i = tab b i)
    (hsep : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ i j, tab b₁ i ≠ tab b₂ j) :
    ∀ b₁ b₂, b₁ ≠ b₂ → ∀ i j,
      ¬ Nonempty (order72_branch_reps b₁ i ≃* order72_branch_reps b₂ j) :=
  order72_cross_branch_disjoint_of_invariant_ne (by
    intro b₁ b₂ hne i j h
    exact hsep b₁ b₂ hne i j (by
      rw [← hspec b₁ i, ← hspec b₂ j]
      exact h))

/-! ### Direct-product branch distinctness -/

noncomputable abbrev order72_direct_reps : Fin 10 → Type
  | 0 => CyclicRep 9 × Multiplicative (ZMod 8)
  | 1 => CyclicRep 9 × H2
  | 2 => CyclicRep 9 × E8
  | 3 => CyclicRep 9 × DihedralGroup 4
  | 4 => CyclicRep 9 × QuaternionGroup 2
  | 5 => ElemAbelianRep 3 × Multiplicative (ZMod 8)
  | 6 => ElemAbelianRep 3 × H2
  | 7 => ElemAbelianRep 3 × E8
  | 8 => ElemAbelianRep 3 × DihedralGroup 4
  | 9 => ElemAbelianRep 3 × QuaternionGroup 2

noncomputable instance order72_direct_reps_group : (i : Fin 10) → Group (order72_direct_reps i)
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
  | 3 => inferInstance
  | 4 => inferInstance
  | 5 => inferInstance
  | 6 => inferInstance
  | 7 => inferInstance
  | 8 => inferInstance
  | 9 => inferInstance
  | ⟨n + 10, h⟩ => by omega

theorem order72_branch_direct_reps_eq (i : Fin 10) :
    order72_branch_reps .direct i = order72_direct_reps i := by
  fin_cases i <;> rfl

noncomputable def order72_direct_invariant (i : Fin 10) : Nat × Nat × Nat × Nat :=
  (Nat.card (Subgroup.center (order72_direct_reps i)),
    order72_pow_eq_one_card (order72_direct_reps i) 2,
    order72_pow_eq_one_card (order72_direct_reps i) 3,
    order72_pow_eq_one_card (order72_direct_reps i) 4)

theorem order72_direct_invariant_eq_of_mulEquiv {i j : Fin 10}
    (hiso : Nonempty (order72_direct_reps i ≃* order72_direct_reps j)) :
    order72_direct_invariant i = order72_direct_invariant j := by
  obtain ⟨e⟩ := hiso
  simp only [order72_direct_invariant]
  exact Prod.ext (card_center_eq_of_mulEquiv e)
    (Prod.ext (order72_pow_eq_one_card_eq_of_mulEquiv 2 e)
      (Prod.ext (order72_pow_eq_one_card_eq_of_mulEquiv 3 e)
        (order72_pow_eq_one_card_eq_of_mulEquiv 4 e)))

def order72_direct_invariant_table : Fin 10 → Nat × Nat × Nat × Nat
  | 0 => (72, 2, 3, 4)
  | 1 => (72, 4, 3, 8)
  | 2 => (72, 8, 3, 8)
  | 3 => (18, 6, 3, 8)
  | 4 => (18, 2, 3, 8)
  | 5 => (72, 2, 9, 4)
  | 6 => (72, 4, 9, 8)
  | 7 => (72, 8, 9, 8)
  | 8 => (18, 6, 9, 8)
  | 9 => (18, 2, 9, 8)

set_option maxHeartbeats 1000000 in
-- Finite kernel computation over the ten concrete direct products.
theorem order72_direct_invariant_spec (i : Fin 10) :
    order72_direct_invariant i = order72_direct_invariant_table i := by
  classical
  fin_cases i <;>
    simp only [order72_direct_invariant, order72_direct_invariant_table,
      order72_direct_reps, order72_pow_eq_one_card,
      Nat.card_eq_fintype_card]
  all_goals
    apply Prod.ext
    · norm_num
      decide +kernel
    · apply Prod.ext
      · norm_num
        decide +kernel
      · apply Prod.ext
        · norm_num
          decide +kernel
        · norm_num
          decide +kernel

theorem order72_direct_invariant_table_injective :
    Function.Injective order72_direct_invariant_table := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [order72_direct_invariant_table] at h ⊢

theorem order72_direct_branch_pairwise :
    PairwiseNonMulEquiv (order72_branch_reps .direct) := by
  have hdirect : PairwiseNonMulEquiv order72_direct_reps := by
    exact PairwiseNonMulEquiv.of_invariant order72_direct_invariant
      (fun _ _ h => order72_direct_invariant_eq_of_mulEquiv h)
      (fun i j h _ =>
        order72_direct_invariant_table_injective (by
          rw [← order72_direct_invariant_spec i, ← order72_direct_invariant_spec j]
          exact h))
  intro i j hiso
  fin_cases i <;> fin_cases j <;>
    exact hdirect _ _ hiso

/-- Once pairwise non-isomorphism of the displayed representatives is known, they form a complete
classification of groups of order `72`. -/
theorem order72_isClassif_of_pairwise (hdistinct : PairwiseNonMulEquiv order72_reps) :
    IsClassif 72 order72_reps where
  card := order72_reps_card
  complete := order72_complete
  distinct := hdistinct

/-- Sigma-style assembly for distinctness: prove pairwise non-isomorphism inside each
bookkeeping branch and disjointness across different branches, then concatenate. -/
theorem order72_sigma_reps_pairwise_of_branches
    (hparts : ∀ b, PairwiseNonMulEquiv (order72_branch_reps b))
    (hdisj : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ i j,
      ¬ Nonempty (order72_branch_reps b₁ i ≃* order72_branch_reps b₂ j)) :
    PairwiseNonMulEquiv order72_sigma_reps := by
  exact PairwiseNonMulEquiv.sigma hparts hdisj

/-- Reindex sigma-style distinctness back to the original `Fin 50` representative list, once the
displayed representatives have been bridged to the sigma representatives. -/
theorem order72_reps_pairwise_of_sigma
    (hsigma : PairwiseNonMulEquiv order72_sigma_reps) :
    PairwiseNonMulEquiv order72_reps := by
  intro i j hiso
  exact order72_index_injective
    (hsigma (order72_index i) (order72_index j) (order72_reps_to_sigma_iso hiso))

/-- Pairwise distinctness of the original representative list from branchwise distinctness and
cross-branch disjointness. -/
theorem order72_reps_pairwise_of_branch_data
    (hparts : ∀ b, PairwiseNonMulEquiv (order72_branch_reps b))
    (hdisj : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ i j,
      ¬ Nonempty (order72_branch_reps b₁ i ≃* order72_branch_reps b₂ j)) :
    PairwiseNonMulEquiv order72_reps :=
  order72_reps_pairwise_of_sigma
    (order72_sigma_reps_pairwise_of_branches hparts hdisj)

theorem order72_reps_pairwise_of_branch_invariants
    (hinj : ∀ b, Function.Injective (order72_branch_invariant b))
    (hsep : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ i j,
      order72_branch_invariant b₁ i ≠ order72_branch_invariant b₂ j) :
    PairwiseNonMulEquiv order72_reps :=
  order72_reps_pairwise_of_branch_data
    (fun b => order72_branch_reps_pairwise_of_invariant_injective b (hinj b))
    (order72_cross_branch_disjoint_of_invariant_ne hsep)

theorem order72_reps_pairwise_of_branch_invariant_tables
    (tab : (b : Order72Branch) → order72_branch_index b → Order72Invariant)
    (hspec : ∀ b i, order72_branch_invariant b i = tab b i)
    (hinj : ∀ b, Function.Injective (tab b))
    (hsep : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ i j, tab b₁ i ≠ tab b₂ j) :
    PairwiseNonMulEquiv order72_reps :=
  order72_reps_pairwise_of_branch_data
    (fun b => order72_branch_reps_pairwise_of_invariant_table b (tab b) (hspec b) (hinj b))
    (order72_cross_branch_disjoint_of_invariant_tables tab hspec hsep)

/-- Final `IsClassif` packaging from branchwise distinctness plus cross-branch disjointness. -/
theorem order72_isClassif_of_branch_data
    (hparts : ∀ b, PairwiseNonMulEquiv (order72_branch_reps b))
    (hdisj : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ i j,
      ¬ Nonempty (order72_branch_reps b₁ i ≃* order72_branch_reps b₂ j)) :
    IsClassif 72 order72_reps :=
  order72_isClassif_of_pairwise
    (order72_reps_pairwise_of_branch_data hparts hdisj)

theorem order72_isClassif_of_invariant_injective
    (hinj : Function.Injective order72_reps_invariant) :
    IsClassif 72 order72_reps :=
  order72_isClassif_of_pairwise
    (order72_reps_pairwise_of_invariant_injective hinj)

theorem order72_isClassif_of_invariant_table
    (tab : Fin 50 → Order72Invariant)
    (hspec : ∀ i, order72_reps_invariant i = tab i)
    (hinj : Function.Injective tab) :
    IsClassif 72 order72_reps :=
  order72_isClassif_of_pairwise
    (order72_reps_pairwise_of_invariant_table tab hspec hinj)

theorem order72_isClassif_of_branch_invariants
    (hinj : ∀ b, Function.Injective (order72_branch_invariant b))
    (hsep : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ i j,
      order72_branch_invariant b₁ i ≠ order72_branch_invariant b₂ j) :
    IsClassif 72 order72_reps :=
  order72_isClassif_of_pairwise
    (order72_reps_pairwise_of_branch_invariants hinj hsep)

theorem order72_isClassif_of_branch_invariant_tables
    (tab : (b : Order72Branch) → order72_branch_index b → Order72Invariant)
    (hspec : ∀ b i, order72_branch_invariant b i = tab b i)
    (hinj : ∀ b, Function.Injective (tab b))
    (hsep : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ i j, tab b₁ i ≠ tab b₂ j) :
    IsClassif 72 order72_reps :=
  order72_isClassif_of_pairwise
    (order72_reps_pairwise_of_branch_invariant_tables tab hspec hinj hsep)

end Smallgroups.UsefulTheorems
