/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order63

/-!
# Classification of groups of order 63

`63 = 7 · 3²`.  There are exactly four groups of order `63` up to isomorphism:
the cyclic group `C₆₃`, the abelian non-cyclic group `C₇ × C₃ × C₃`, the non-abelian group
`(C₇ ⋊ C₃) × C₃`, and the non-abelian group `C₇ ⋊ C₉`.
-/

namespace Smallgroups.Classifications.Order63

open Smallgroups.UsefulTheorems

/-- `C₆₃`. -/
abbrev RA : Type := order63_RA
/-- `C₇ × C₃ × C₃`. -/
abbrev RB : Type := order63_RB
/-- `(C₇ ⋊ C₃) × C₃`. -/
abbrev RC : Type := order63_RC
/-- `C₇ ⋊ C₉`, where the action has image of order `3`. -/
abbrev RD : Type := order63_RD

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `63` is isomorphic to one of the four groups. -/
theorem classification (h : Nat.card G = 63) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨ Nonempty (G ≃* RD) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [RA, RB, RC, RD] using order63_classification (G := G) h

private theorem classif_bundle : IsClassif 63 (rep4 RA RB RC RD) where
  card i := by
    fin_cases i
    · exact card_order63_RA
    · exact card_order63_RB
    · exact card_order63_RC
    · exact card_order63_RD
  complete G _ hG := by
    haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
    rcases order63_classification (G := G) hG with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  distinct i j h := by
    simpa [RA, RB, RC, RD] using order63_pairwise i j h

/-- **(2) Distinctness.** The four groups are pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (rep4 RA RB RC RD i ≃* rep4 RA RB RC RD j) → i = j :=
  classif_bundle.distinct

/-- **(3) Counting.** The four groups are a complete, non-redundant list of representatives of
the groups of order `63`. -/
theorem isClassif : IsClassif 63 (rep4 RA RB RC RD) := classif_bundle

/-- **The number of isomorphism classes of groups of order `63` is exactly `4`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 63 rep) : k = 4 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order63
