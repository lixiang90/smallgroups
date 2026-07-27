/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.SmallGroup
import Smallgroups.GAP.Polycyclic.Imported.Order49Match
import Smallgroups.Classifications.Classifications_41_to_50.Order49

/-!
# GAP-numbered classification of groups of order 49

`SmallGroup(49, 1) = ℤ/49` and `SmallGroup(49, 2) = ℤ/7 × ℤ/7`, matching
the order of the project's existing list.  The representatives are the imported pc
groups `smallGroup 49 j`; the isomorphisms are certified in
`Polycyclic/Imported/Order49Match.lean`.

* `classification` — (1) exhaustiveness: every group of order `49` is isomorphic
  to `SmallGroup(49, j)` for some `j`.
* `distinct` — (2) distinctness: the two classes are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: exactly two isomorphism classes.
-/

namespace Smallgroups.GAP_Classifications.Order49

open Smallgroups.GAP Smallgroups.UsefulTheorems

/-- The GAP-numbered representatives of order `49`: `SmallGroup(49, j)`,
`j = 1, 2`. -/
abbrev gapRep : Fin 2 → Type := rep2 (smallGroup 49 1) (smallGroup 49 2)

/-- The GAP representatives are isomorphic, index by index, to the existing list. -/
private noncomputable def gapEquivs :
    ∀ i, gapRep i ≃* rep2 (CyclicRep 49) (ElemAbelianRep 7) i
  | 0 => order49_1_equiv
  | 1 => order49_2_equiv

/-- **(1)+(2)+(3).** The GAP-numbered list `[SmallGroup(49, 1), SmallGroup(49, 2)]`
is a complete, non-redundant representative list of the groups of order `49`. -/
theorem isClassif : IsClassif 49 gapRep :=
  IsClassif.of_equivs Smallgroups.Classifications.Order49.isClassif gapEquivs

/-- **(1) Exhaustiveness.** Every group of order `49` is isomorphic to
`SmallGroup(49, j)` for some `j`. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 49) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  isClassif.complete G h

/-- **(2) Distinctness.** `SmallGroup(49, 1)` and `SmallGroup(49, 2)` are not
isomorphic. -/
theorem distinct {i j : Fin 2} (hij : i ≠ j) : ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- **(3) Counting.** The number of isomorphism classes of groups of order `49` is
exactly `2`, the GAP SmallGroups library count. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 49 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order49
