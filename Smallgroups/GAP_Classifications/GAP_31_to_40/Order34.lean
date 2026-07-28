/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.SmallGroup
import Smallgroups.GAP.Polycyclic.Imported.Order34Match
import Smallgroups.Classifications.Classifications_31_to_40.Order34

/-!
# GAP-numbered classification of groups of order 34

`SmallGroup(34, 1) = DihedralGroup 17` and `SmallGroup(34, 2) = ℤ/34`.
The representatives are the imported pc groups `smallGroup 34 j`.
-/

namespace Smallgroups.GAP_Classifications.Order34

open Smallgroups.GAP Smallgroups.UsefulTheorems

/-- The GAP-numbered representatives of order `34`. -/
abbrev gapRep : Fin 2 → Type := rep2 (smallGroup 34 1) (smallGroup 34 2)

/-- Swapping the existing list puts it in GAP order. -/
private def swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

/-- The GAP representatives match the permuted existing list. -/
private noncomputable def gapEquivs :
    ∀ i, gapRep i ≃* rep2 (CyclicRep 34) (DihedralGroup 17) (swap i)
  | 0 => order34_1_equiv
  | 1 => order34_2_equiv

/-- **(1)+(2)+(3).** The GAP-numbered list `[SmallGroup(34, 1), SmallGroup(34, 2)]`
is complete and non-redundant. -/
theorem isClassif : IsClassif 34 gapRep :=
  IsClassif.of_equivs
    (IsClassif.of_perm Smallgroups.Classifications.Order34.isClassif swap) gapEquivs

/-- **(1) Exhaustiveness.** Every group of order `34` is isomorphic to a GAP
representative. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 34) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  isClassif.complete G h

/-- **(2) Distinctness.** Different GAP indices give non-isomorphic groups. -/
theorem distinct {i j : Fin 2} (hij : i ≠ j) :
    ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- **(3) Counting.** There are exactly `2` isomorphism classes. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 34 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order34
