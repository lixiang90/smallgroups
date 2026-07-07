/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order60.Classification
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# Classification of groups of order 60

`60 = 5 · 12`, so there are exactly **thirteen** groups of order `60` up to isomorphism:
the twelve solvable representatives from `Order60.Semiproduct` and the simple alternating
group `A₅`.

* `classification` — (1) exhaustiveness: every group of order `60` is isomorphic to one of the
  thirteen representatives.
* `distinct` — (2) distinctness: the thirteen representatives are pairwise non-isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly thirteen isomorphism classes.
-/

namespace Smallgroups.Classifications.Order60

open Smallgroups.UsefulTheorems

/-- `ℤ/5 × ℤ/12 ≅ ℤ/60` (trivial action on the cyclic `K = ℤ/12`). -/
abbrev RA : Type := sixtyReps 0
/-- `ℤ/5 × (ℤ/2 × ℤ/6) ≅ ℤ/2 × ℤ/30` (trivial action on `K = ℤ/2 × ℤ/6`). -/
abbrev RB : Type := sixtyReps 1
/-- `ℤ/5 × Dic₃` (trivial action on `K = Dic₃`). -/
abbrev RC : Type := sixtyReps 2
/-- `ℤ/5 × (ℤ/2 × D₆)` (trivial action on `K = ℤ/2 × D₆`). -/
abbrev RD : Type := sixtyReps 3
/-- `ℤ/5 × A₄` (the only action `A₄` admits, since `Aut(A₄) → Aut(ℤ/5)` factors through
`A₄`'s abelianization `ℤ/3`, coprime to `4`). -/
abbrev RE : Type := sixtyReps 4
/-- `ℤ/5 ⋊ ℤ/12` with the order-`2` (non-faithful) action `x ↦ -x`. -/
abbrev RF : Type := sixtyReps 5
/-- `ℤ/5 ⋊ ℤ/12` with the faithful order-`4` action `x ↦ 2x`. -/
abbrev RG : Type := sixtyReps 6
/-- `ℤ/5 ⋊ (ℤ/2 × ℤ/6)` with the order-`2` action through the `ℤ/2` factor. -/
abbrev RH : Type := sixtyReps 7
/-- `ℤ/5 ⋊ Dic₃` with the order-`2` action (through `Dic₃`'s `ℤ/4`-quotient inverting). -/
abbrev RI : Type := sixtyReps 8
/-- `ℤ/5 ⋊ Dic₃` with the faithful order-`4` action. -/
abbrev RJ : Type := sixtyReps 9
/-- `ℤ/5 ⋊ (ℤ/2 × D₆)` with the order-`2` action through the `ℤ/2` factor: `D₁₀ × D₆`. -/
abbrev RK : Type := sixtyReps 10
/-- `ℤ/5 ⋊ (ℤ/2 × D₆)` with the sign action (reflections invert `ℤ/5`):
the dihedral group `D₆₀ ≅ ℤ/2 × D₃₀`. -/
abbrev RL : Type := sixtyReps 11
/-- The alternating group `A₅`, the unique non-solvable group of order `60`. -/
abbrev RM : Type := sixtyReps 12

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `60` is isomorphic to one of the
thirteen representatives. -/
theorem classification (h : Nat.card G = 60) :
    Nonempty (G ≃* RA) ∨ Nonempty (G ≃* RB) ∨ Nonempty (G ≃* RC) ∨ Nonempty (G ≃* RD) ∨
    Nonempty (G ≃* RE) ∨ Nonempty (G ≃* RF) ∨ Nonempty (G ≃* RG) ∨ Nonempty (G ≃* RH) ∨
    Nonempty (G ≃* RI) ∨ Nonempty (G ≃* RJ) ∨ Nonempty (G ≃* RK) ∨ Nonempty (G ≃* RL) ∨
    Nonempty (G ≃* RM) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  exact sixty_classification h

private theorem classif_bundle : IsClassif 60 sixtyReps := sixty_isClassif

/-- **(2) Distinctness.** The thirteen representatives of order `60` are
pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (sixtyReps i ≃* sixtyReps j) → i = j :=
  classif_bundle.distinct

/-- **(3) Counting.** The thirteen representatives form a complete classification of
groups of order `60`. -/
theorem isClassif : IsClassif 60 sixtyReps := classif_bundle

/-- **The number of isomorphism classes of groups of order `60` is exactly `13`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 60 rep) : k = 13 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order60
