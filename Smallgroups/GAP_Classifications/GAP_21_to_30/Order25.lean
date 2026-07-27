/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.SmallGroup
import Smallgroups.GAP.Polycyclic.Imported.Order25Match
import Smallgroups.Classifications.Classifications_21_to_30.Order25

/-!
# GAP-numbered classification of groups of order 25

`SmallGroup(25, 1) = ℤ/25` and `SmallGroup(25, 2) = ℤ/5 × ℤ/5`, matching
the order of the project's existing list.  The representatives are the imported pc
groups `smallGroup 25 j`; the isomorphisms are certified in
`Polycyclic/Imported/Order25Match.lean`.

* `classification` — (1) exhaustiveness: every group of order `25` is isomorphic
  to `SmallGroup(25, j)` for some `j`.
* `distinct` — (2) distinctness: the two classes are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: exactly two isomorphism classes.
-/

namespace Smallgroups.GAP_Classifications.Order25

open Smallgroups.GAP Smallgroups.UsefulTheorems

/-- The GAP-numbered representatives of order `25`: `SmallGroup(25, j)`,
`j = 1, 2`. -/
abbrev gapRep : Fin 2 → Type := rep2 (smallGroup 25 1) (smallGroup 25 2)

/-- The GAP representatives are isomorphic, index by index, to the existing list. -/
private noncomputable def gapEquivs :
    ∀ i, gapRep i ≃* rep2 (CyclicRep 25) (ElemAbelianRep 5) i
  | 0 => order25_1_equiv
  | 1 => order25_2_equiv

/-- **(1)+(2)+(3).** The GAP-numbered list `[SmallGroup(25, 1), SmallGroup(25, 2)]`
is a complete, non-redundant representative list of the groups of order `25`. -/
theorem isClassif : IsClassif 25 gapRep :=
  IsClassif.of_equivs Smallgroups.Classifications.Order25.isClassif gapEquivs

/-- **(1) Exhaustiveness.** Every group of order `25` is isomorphic to
`SmallGroup(25, j)` for some `j`. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 25) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  isClassif.complete G h

/-- **(2) Distinctness.** `SmallGroup(25, 1)` and `SmallGroup(25, 2)` are not
isomorphic. -/
theorem distinct {i j : Fin 2} (hij : i ≠ j) : ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- **(3) Counting.** The number of isomorphism classes of groups of order `25` is
exactly `2`, the GAP SmallGroups library count. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 25 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order25
