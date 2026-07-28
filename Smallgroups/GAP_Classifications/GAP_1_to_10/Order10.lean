/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.SmallGroup
import Smallgroups.GAP.Polycyclic.Imported.Order10Match
import Smallgroups.Classifications.Classifications_1_to_10.Order10

/-!
# GAP-numbered classification of groups of order 10

`SmallGroup(10, 1) = DihedralGroup 5` and `SmallGroup(10, 2) = ℤ/10`.  This
reverses the order of the project's existing list.  The representatives are the
imported pc groups `smallGroup 10 j`; the isomorphisms are certified in
`Polycyclic/Imported/Order10Match.lean`.

* `classification` — (1) exhaustiveness: every group of order `10` is isomorphic
  to `SmallGroup(10, j)` for some `j`.
* `distinct` — (2) distinctness: the two classes are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: exactly two isomorphism classes.
-/

namespace Smallgroups.GAP_Classifications.Order10

open Smallgroups.GAP Smallgroups.UsefulTheorems

/-- The GAP-numbered representatives of order `10`: `SmallGroup(10, 1)` is
dihedral and `SmallGroup(10, 2)` is cyclic. -/
abbrev gapRep : Fin 2 → Type := rep2 (smallGroup 10 1) (smallGroup 10 2)

/-- Swapping the existing cyclic/dihedral list puts it in GAP order. -/
private def swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

/-- The GAP representatives are isomorphic, index by index, to the permuted
existing list. -/
private noncomputable def gapEquivs :
    ∀ i, gapRep i ≃* rep2 (CyclicRep 10) (DihedralGroup 5) (swap i)
  | 0 => order10_1_equiv
  | 1 => order10_2_equiv

/-- **(1)+(2)+(3).** The GAP-numbered list
`[SmallGroup(10, 1), SmallGroup(10, 2)]` is a complete, non-redundant
representative list of the groups of order `10`. -/
theorem isClassif : IsClassif 10 gapRep :=
  IsClassif.of_equivs
    (IsClassif.of_perm Smallgroups.Classifications.Order10.isClassif swap) gapEquivs

/-- **(1) Exhaustiveness.** Every group of order `10` is isomorphic to
`SmallGroup(10, j)` for some `j`. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 10) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  isClassif.complete G h

/-- **(2) Distinctness.** The two GAP-numbered groups of order `10` are not
isomorphic. -/
theorem distinct {i j : Fin 2} (hij : i ≠ j) : ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- **(3) Counting.** The number of isomorphism classes of groups of order `10`
is exactly `2`, the GAP SmallGroups library count. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 10 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order10
