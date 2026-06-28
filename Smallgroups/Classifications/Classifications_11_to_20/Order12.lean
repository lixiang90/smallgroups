/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P_12
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 12

`12 = 4 · 3`, so there are exactly **five** groups of order `12` up to isomorphism:
the cyclic group `ℤ/12`, `ℤ/2 × ℤ/6`, `ℤ/3 ⋊_{-1} ℤ/4` (a.k.a. `Dic₃`),
`ℤ/2 × D₆` (equivalently `ℤ/2 × S₃`), and the alternating group `A₄`.
This is the special `p = 3` case of the order-`4p` classification in
`Smallgroups.UsefulTheorems.Order4P_12`.
-/

namespace Smallgroups.Classifications.Order12

open Smallgroups.UsefulTheorems

/-- `ℤ/12`. -/
abbrev RA : Type := fourP_I 3
/-- `ℤ/2 × ℤ/6`. -/
abbrev RB : Type := fourP_II 3
/-- `ℤ/3 ⋊_{-1} ℤ/4` (dicyclic group `Dic₃`). -/
abbrev RC : Type := fourP_III 3
/-- `ℤ/2 × D₆` (equivalently `ℤ/2 × S₃`). -/
abbrev RD : Type := fourP_V 3
/-- The alternating group `A₄`. -/
abbrev RE : Type := fourP_A4

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `12` is isomorphic to one of the five groups. -/
theorem classification (h : Nat.card G = 12) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨ Nonempty (G ≃* RD) ∨
      Nonempty (G ≃* RE) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  exact fourP_12_classification h

private theorem classif_bundle : IsClassif 12 (rep5 RA RB RC RD RE) :=
  fourP_12_isClassif

/-- **(2) Distinctness.** The five groups are pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (rep5 RA RB RC RD RE i ≃* rep5 RA RB RC RD RE j) → i = j :=
  classif_bundle.distinct

/-- **(3) Counting.** The five groups are a complete, non-redundant list of
representatives of the groups of order `12`. -/
theorem isClassif : IsClassif 12 (rep5 RA RB RC RD RE) := classif_bundle

/-- **The number of isomorphism classes of groups of order `12` is exactly `5`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 12 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order12
