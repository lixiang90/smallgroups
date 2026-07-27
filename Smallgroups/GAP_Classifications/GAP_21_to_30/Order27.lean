/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.SmallGroup
import Smallgroups.GAP.Polycyclic.Imported.Order27Match
import Smallgroups.Classifications.Classifications_21_to_30.Order27

/-!
# GAP-numbered classification of groups of order 27

The GAP SmallGroups library order for order `27` is

`SmallGroup(27, 1) = ℤ/27`, `SmallGroup(27, 2) = ℤ/9 × ℤ/3`,
`SmallGroup(27, 3)` = the Heisenberg group, `SmallGroup(27, 4) = ℤ/9 ⋊ ℤ/3`,
`SmallGroup(27, 5) = (ℤ/3)³`,

which differs from the project's existing order-`27` list
`[ℤ/27, ℤ/9×ℤ/3, (ℤ/3)³, Heisenberg, ℤ/9⋊ℤ/3]` by a permutation of the last three
entries.  The representatives are the imported pc groups `smallGroup 27 j`
(`GAP/SmallGroup.lean`); the isomorphisms to the existing representatives are
certified in `Polycyclic/Imported/Order27Match.lean`.

* `classification` — (1) exhaustiveness: every group of order `27` is isomorphic to
  `SmallGroup(27, j)` for some `j`.
* `distinct` — (2) distinctness: the `SmallGroup(27, j)` are pairwise non-isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: exactly five isomorphism classes.
-/

namespace Smallgroups.GAP_Classifications.Order27

open Smallgroups.GAP Smallgroups.UsefulTheorems


/-- The GAP-numbered representatives of order `27`: `SmallGroup(27, j)`, `j = 1, …, 5`. -/
abbrev gapRep : Fin 5 → Type :=
  rep5 (smallGroup 27 1) (smallGroup 27 2) (smallGroup 27 3) (smallGroup 27 4)
    (smallGroup 27 5)

/-- The permutation aligning the existing order-`27` list
`[ℤ/27, ℤ/9×ℤ/3, (ℤ/3)³, Heisenberg, ℤ/9⋊ℤ/3]` with the GAP numbering
`[ℤ/27, ℤ/9×ℤ/3, Heisenberg, ℤ/9⋊ℤ/3, (ℤ/3)³]`. -/
private def perm27 : Fin 5 ≃ Fin 5 :=
  (Equiv.swap ⟨3, by decide⟩ ⟨4, by decide⟩).trans (Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩)

/-- The GAP representatives are isomorphic, index by index, to the permuted existing list. -/
private noncomputable def gapEquivs : ∀ i, gapRep i ≃*
    rep5 Smallgroups.Classifications.Order27.RA Smallgroups.Classifications.Order27.RB
      Smallgroups.Classifications.Order27.RC Smallgroups.Classifications.Order27.RD
      Smallgroups.Classifications.Order27.RE (perm27 i)
  | 0 => order27_1_equiv
  | 1 => order27_2_equiv
  | 2 => order27_3_equiv
  | 3 => order27_4_equiv
  | 4 => order27_5_equiv

/-- **(1)+(2)+(3).** The GAP-numbered list `[SmallGroup(27, 1), …, SmallGroup(27, 5)]`
is a complete, non-redundant representative list of the groups of order `27`. -/
theorem isClassif : IsClassif 27 gapRep :=
  IsClassif.of_equivs
    (IsClassif.of_perm Smallgroups.Classifications.Order27.isClassif perm27) gapEquivs

/-- **(1) Exhaustiveness.** Every group of order `27` is isomorphic to
`SmallGroup(27, j)` for some `j`. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 27) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  isClassif.complete G h

/-- **(2) Distinctness.** The `SmallGroup(27, j)` are pairwise non-isomorphic. -/
theorem distinct {i j : Fin 5} (hij : i ≠ j) : ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- **(3) Counting.** The number of isomorphism classes of groups of order `27` is
exactly `5`, the GAP SmallGroups library count. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 27 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order27
