/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.SmallGroup
import Smallgroups.GAP.Polycyclic.Imported.Order74Match
import Smallgroups.Classifications.Classifications_71_to_80.Order74

/-!
# GAP-numbered classification of groups of order 74

`SmallGroup(74, 1) = DihedralGroup 37` and `SmallGroup(74, 2) = ℤ/74`.
The representatives are the imported pc groups `smallGroup 74 j`.
-/

namespace Smallgroups.GAP_Classifications.Order74

open Smallgroups.GAP Smallgroups.UsefulTheorems

/-- The GAP-numbered representatives of order `74`. -/
abbrev gapRep : Fin 2 → Type := rep2 (smallGroup 74 1) (smallGroup 74 2)

/-- Swapping the existing list puts it in GAP order. -/
private def swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

/-- The GAP representatives match the permuted existing list. -/
private noncomputable def gapEquivs :
    ∀ i, gapRep i ≃* rep2 (CyclicRep 74) (DihedralGroup 37) (swap i)
  | 0 => order74_1_equiv
  | 1 => order74_2_equiv

/-- **(1)+(2)+(3).** The GAP-numbered list `[SmallGroup(74, 1), SmallGroup(74, 2)]`
is complete and non-redundant. -/
theorem isClassif : IsClassif 74 gapRep :=
  IsClassif.of_equivs
    (IsClassif.of_perm Smallgroups.Classifications.Order74.isClassif swap) gapEquivs

/-- **(1) Exhaustiveness.** Every group of order `74` is isomorphic to a GAP
representative. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 74) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  isClassif.complete G h

/-- **(2) Distinctness.** Different GAP indices give non-isomorphic groups. -/
theorem distinct {i j : Fin 2} (hij : i ≠ j) :
    ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- **(3) Counting.** There are exactly `2` isomorphism classes. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 74 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order74
