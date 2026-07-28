/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.SmallGroup
import Smallgroups.GAP.Polycyclic.Imported.Order93Match
import Smallgroups.Classifications.Classifications_91_to_100.Order93

/-!
# GAP-numbered classification of groups of order 93

`SmallGroup(93, 1)` is nonabelian and `SmallGroup(93, 2) = ℤ/93`.
The representatives are the imported pc groups `smallGroup 93 j`.
-/

namespace Smallgroups.GAP_Classifications.Order93

open Smallgroups.GAP Smallgroups.UsefulTheorems

/-- The GAP-numbered representatives of order `93`. -/
abbrev gapRep : Fin 2 → Type := rep2 (smallGroup 93 1) (smallGroup 93 2)

/-- Swapping the existing list puts it in GAP order. -/
private def swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

/-- The GAP representatives match the permuted existing list. -/
private noncomputable def gapEquivs :
    ∀ i, gapRep i ≃* rep2 (CyclicRep 93) (Smallgroups.Classifications.Order93.NonabRep93) (swap i)
  | 0 => order93_1_equiv
  | 1 => order93_2_equiv

/-- **(1)+(2)+(3).** The GAP-numbered list `[SmallGroup(93, 1), SmallGroup(93, 2)]`
is complete and non-redundant. -/
theorem isClassif : IsClassif 93 gapRep :=
  IsClassif.of_equivs
    (IsClassif.of_perm Smallgroups.Classifications.Order93.isClassif swap) gapEquivs

/-- **(1) Exhaustiveness.** Every group of order `93` is isomorphic to a GAP
representative. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 93) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  isClassif.complete G h

/-- **(2) Distinctness.** Different GAP indices give non-isomorphic groups. -/
theorem distinct {i j : Fin 2} (hij : i ≠ j) :
    ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- **(3) Counting.** There are exactly `2` isomorphism classes. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 93 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order93
