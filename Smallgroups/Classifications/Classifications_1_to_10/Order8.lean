/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.P3Group
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 8

`8 = 2³`, so there are exactly **five** groups of order `8` up to isomorphism:
the cyclic group `ℤ/8`, `ℤ/4 × ℤ/2`, the elementary abelian `(ℤ/2)³`, the dihedral group `D₄`,
and the quaternion group `Q₈`. This is the `p = 2` instance of the order-`p³` classification in
`Smallgroups.UsefulTheorems.P3Group`.
-/

namespace Smallgroups.Classifications.Order8

open Smallgroups.UsefulTheorems P3Group

/-- `ℤ/8`. -/
abbrev RA : Type := Multiplicative (CyclicP3 2)
/-- `ℤ/4 × ℤ/2`. -/
abbrev RB : Type := Multiplicative (ZMod (2 ^ 2)) × Multiplicative (ZMod 2)
/-- `(ℤ/2)³`. -/
abbrev RC : Type := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
/-- The dihedral group `D₄`. -/
abbrev RD : Type := DihedralGroup 4
/-- The quaternion group `Q₈`. -/
abbrev RE : Type := QuaternionGroup 2

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `8` is isomorphic to one of the five groups. -/
theorem classification (h : Nat.card G = 8) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨ Nonempty (G ≃* RD) ∨
      Nonempty (G ≃* RE) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  haveI : Fintype G := Fintype.ofFinite G
  rcases P3Group.classification 2 G (h.trans (by norm_num)) with h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact (h1.1 rfl).elim
  · exact (h1.1 rfl).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1.2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1.2)))

private theorem classif_bundle : IsClassif 8 (rep5 RA RB RC RD RE) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact isClassif_five RA RB RC RD RE
    (card_cyclicP3 2) (card_abelianP2P 2) (card_elementaryP3 2) card_dihedral4 card_quaternion8
    (fun _ _ hG => classification hG)
    (not_nonempty_iff.mpr (abelian_types_distinct 2).1)
    (not_nonempty_iff.mpr (abelian_types_distinct 2).2.1)
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b) dihedral4_nonabelian)
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b) quaternion8_nonabelian)
    (not_nonempty_iff.mpr (abelian_types_distinct 2).2.2)
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b) dihedral4_nonabelian)
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b) quaternion8_nonabelian)
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b) dihedral4_nonabelian)
    (isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b) quaternion8_nonabelian)
    (not_nonempty_iff.mpr dihedral4_not_iso_quaternion8)

/-- **(2) Distinctness.** The five groups are pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (rep5 RA RB RC RD RE i ≃* rep5 RA RB RC RD RE j) → i = j :=
  classif_bundle.distinct

/-- **(3) Counting.** The five groups are a complete, non-redundant list of
representatives of the groups of order `8`. -/
theorem isClassif : IsClassif 8 (rep5 RA RB RC RD RE) := classif_bundle

/-- **The number of isomorphism classes of groups of order `8` is exactly `5`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 8 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order8
