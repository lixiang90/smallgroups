/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.P3Group
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 27

`27 = 3³`, so there are exactly **five** groups of order `27` up to isomorphism:
the cyclic group `ℤ/27`, `ℤ/9 × ℤ/3`, the elementary abelian `(ℤ/3)³`, the Heisenberg group
(exponent `3`), and `ℤ/9 ⋊ ℤ/3` (exponent `9`). This is the `p = 3` instance of the order-`p³`
classification in `Smallgroups.UsefulTheorems.P3Group`.
-/

namespace Smallgroups.Classifications.Order27

open Smallgroups.UsefulTheorems P3Group

/-- `ℤ/27`. -/
abbrev RA : Type := Multiplicative (CyclicP3 3)
/-- `ℤ/9 × ℤ/3`. -/
abbrev RB : Type := Multiplicative (ZMod (3 ^ 2)) × Multiplicative (ZMod 3)
/-- `(ℤ/3)³`. -/
abbrev RC : Type := Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3)
/-- The Heisenberg group (non-abelian, exponent `3`). -/
abbrev RD : Type := HeisenbergGroup 3
/-- `ℤ/9 ⋊ ℤ/3` (non-abelian, exponent `9`). -/
abbrev RE : Type := SemidirectP2P 3

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `27` is isomorphic to one of the five groups. -/
theorem classification (h : Nat.card G = 27) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨ Nonempty (G ≃* RD) ∨
      Nonempty (G ≃* RE) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  haveI : Fintype G := Fintype.ofFinite G
  rcases P3Group.classification 3 G (h.trans (by norm_num)) with h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1.2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1.2)))
  · exact absurd h1.1 (by norm_num)
  · exact absurd h1.1 (by norm_num)

private theorem classif_bundle : IsClassif 27 (rep5 RA RB RC RD RE) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact isClassif_five RA RB RC RD RE
    (card_cyclicP3 3) (card_abelianP2P 3) (card_elementaryP3 3) (HeisenbergGroup.card_heisenberg 3)
    (SemidirectP2P.card_semidirectP2P 3)
    (fun _ _ hG => classification hG)
    (not_nonempty_iff.mpr (abelian_types_distinct 3).1)
    (not_nonempty_iff.mpr (abelian_types_distinct 3).2.1)
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b)
      (HeisenbergGroup.heisenberg_nonabelian 3))
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b)
      (SemidirectP2P.semidirectP2P_nonabelian 3))
    (not_nonempty_iff.mpr (abelian_types_distinct 3).2.2)
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b)
      (HeisenbergGroup.heisenberg_nonabelian 3))
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b)
      (SemidirectP2P.semidirectP2P_nonabelian 3))
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b)
      (HeisenbergGroup.heisenberg_nonabelian 3))
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b)
      (SemidirectP2P.semidirectP2P_nonabelian 3))
    (not_nonempty_iff.mpr (heisenberg_not_iso_semidirect 3 (by norm_num)))

/-- **(2) Distinctness.** The five groups are pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (rep5 RA RB RC RD RE i ≃* rep5 RA RB RC RD RE j) → i = j :=
  classif_bundle.distinct

/-- **(3) Counting.** The five groups are a complete, non-redundant list of
representatives of the groups of order `27`. -/
theorem isClassif : IsClassif 27 (rep5 RA RB RC RD RE) := classif_bundle

/-- **The number of isomorphism classes of groups of order `27` is exactly `5`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 27 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order27
