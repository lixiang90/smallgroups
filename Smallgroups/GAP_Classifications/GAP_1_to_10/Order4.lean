/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.SmallGroup
import Smallgroups.GAP.Polycyclic.Imported.Order4Match
import Smallgroups.Classifications.Classifications_1_to_10.Order4

/-!
# GAP-numbered classification of groups of order 4

`SmallGroup(4, 1) = ℤ/4` and `SmallGroup(4, 2) = ℤ/2 × ℤ/2`, matching
the order of the project's existing list.  The representatives are the imported pc
groups `smallGroup 4 j`; the isomorphisms are certified in
`Polycyclic/Imported/Order4Match.lean`.

* `classification` — (1) exhaustiveness: every group of order `4` is isomorphic
  to `SmallGroup(4, j)` for some `j`.
* `distinct` — (2) distinctness: the two classes are not isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: exactly two isomorphism classes.
-/

namespace Smallgroups.GAP_Classifications.Order4

open Smallgroups.GAP Smallgroups.UsefulTheorems

/-- The GAP-numbered representatives of order `4`: `SmallGroup(4, j)`,
`j = 1, 2`. -/
abbrev gapRep : Fin 2 → Type := rep2 (smallGroup 4 1) (smallGroup 4 2)

/-- The GAP representatives are isomorphic, index by index, to the existing list. -/
private noncomputable def gapEquivs :
    ∀ i, gapRep i ≃* rep2 (CyclicRep 4) (ElemAbelianRep 2) i
  | 0 => order4_1_equiv
  | 1 => order4_2_equiv

/-- **(1)+(2)+(3).** The GAP-numbered list `[SmallGroup(4, 1), SmallGroup(4, 2)]`
is a complete, non-redundant representative list of the groups of order `4`. -/
theorem isClassif : IsClassif 4 gapRep :=
  IsClassif.of_equivs Smallgroups.Classifications.Order4.isClassif gapEquivs

/-- **(1) Exhaustiveness.** Every group of order `4` is isomorphic to
`SmallGroup(4, j)` for some `j`. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 4) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  isClassif.complete G h

/-- **(2) Distinctness.** `SmallGroup(4, 1)` and `SmallGroup(4, 2)` are not
isomorphic. -/
theorem distinct {i j : Fin 2} (hij : i ≠ j) : ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- **(3) Counting.** The number of isomorphism classes of groups of order `4` is
exactly `2`, the GAP SmallGroups library count. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 4 rep) : k = 2 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order4
