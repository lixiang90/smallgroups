/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.SmallGroup
import Smallgroups.GAP.Polycyclic.Imported.Order77Match
import Smallgroups.Classifications.Classifications_71_to_80.Order77

/-!
# GAP-numbered classification of groups of order 77

`SmallGroup(77, 1) = ℤ/77`.
The representatives are the imported pc groups `smallGroup 77 j`.
-/

namespace Smallgroups.GAP_Classifications.Order77

open Smallgroups.GAP Smallgroups.UsefulTheorems

/-- The GAP-numbered representatives of order `77`. -/
abbrev gapRep : Fin 1 → Type := rep1 (smallGroup 77 1)

/-- The GAP representatives match the existing list. -/
private noncomputable def gapEquivs :
    ∀ i, gapRep i ≃* rep1 (CyclicRep 77) i
  | 0 => order77_1_equiv

/-- **(1)+(2)+(3).** The GAP-numbered list `[SmallGroup(77, 1)]`
is complete and non-redundant. -/
theorem isClassif : IsClassif 77 gapRep :=
  IsClassif.of_equivs
    (Smallgroups.Classifications.Order77.isClassif) gapEquivs

/-- **(1) Exhaustiveness.** Every group of order `77` is isomorphic to a GAP
representative. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 77) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  isClassif.complete G h

/-- **(2) Distinctness.** Different GAP indices give non-isomorphic groups. -/
theorem distinct {i j : Fin 1} (hij : i ≠ j) :
    ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- **(3) Counting.** There are exactly `1` isomorphism classes. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 77 rep) : k = 1 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order77
