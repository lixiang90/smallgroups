/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.SmallGroup
import Smallgroups.GAP.Polycyclic.Imported.Order8Match
import Smallgroups.Classifications.Classifications_1_to_10.Order8

/-!
# GAP-numbered classification of groups of order 8

The GAP SmallGroups library order for order `8` is

`SmallGroup(8, 1) = ℤ/8`, `SmallGroup(8, 2) = ℤ/4 × ℤ/2`, `SmallGroup(8, 3) = D₄`,
`SmallGroup(8, 4) = Q₈`, `SmallGroup(8, 5) = (ℤ/2)³`,

which differs from the project's existing order-`8` list `[ℤ/8, ℤ/4×ℤ/2, (ℤ/2)³, D₄, Q₈]`
by a permutation of the last three entries.  The representatives are the imported
pc groups `smallGroup 8 j` (`GAP/SmallGroup.lean`); the isomorphisms to the existing
representatives are certified in `Polycyclic/Imported/Order8Match.lean`.

* `classification` — (1) exhaustiveness: every group of order `8` is isomorphic to
  `SmallGroup(8, j)` for some `j`.
* `distinct` — (2) distinctness: the `SmallGroup(8, j)` are pairwise non-isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: exactly five isomorphism classes.
-/

namespace Smallgroups.GAP_Classifications.Order8

open Smallgroups.GAP Smallgroups.UsefulTheorems


/-- The GAP-numbered representatives of order `8`: `SmallGroup(8, j)`, `j = 1, …, 5`. -/
abbrev gapRep : Fin 5 → Type :=
  rep5 (smallGroup 8 1) (smallGroup 8 2) (smallGroup 8 3) (smallGroup 8 4) (smallGroup 8 5)

/-- The permutation aligning the existing order-`8` list `[ℤ/8, ℤ/4×ℤ/2, (ℤ/2)³, D₄, Q₈]`
with the GAP numbering `[ℤ/8, ℤ/4×ℤ/2, D₄, Q₈, (ℤ/2)³]`. -/
private def perm8 : Fin 5 ≃ Fin 5 :=
  (Equiv.swap ⟨3, by decide⟩ ⟨4, by decide⟩).trans (Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩)

/-- The GAP representatives are isomorphic, index by index, to the permuted existing list. -/
private noncomputable def gapEquivs : ∀ i, gapRep i ≃*
    rep5 Smallgroups.Classifications.Order8.RA Smallgroups.Classifications.Order8.RB
      Smallgroups.Classifications.Order8.RC Smallgroups.Classifications.Order8.RD
      Smallgroups.Classifications.Order8.RE (perm8 i)
  | 0 => order8_1_equiv
  | 1 => order8_2_equiv
  | 2 => order8_3_equiv
  | 3 => order8_4_equiv
  | 4 => order8_5_equiv

/-- **(1)+(2)+(3).** The GAP-numbered list `[SmallGroup(8, 1), …, SmallGroup(8, 5)]`
is a complete, non-redundant representative list of the groups of order `8`. -/
theorem isClassif : IsClassif 8 gapRep :=
  IsClassif.of_equivs
    (IsClassif.of_perm Smallgroups.Classifications.Order8.isClassif perm8) gapEquivs

/-- **(1) Exhaustiveness.** Every group of order `8` is isomorphic to `SmallGroup(8, j)`
for some `j`. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 8) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  isClassif.complete G h

/-- **(2) Distinctness.** The `SmallGroup(8, j)` are pairwise non-isomorphic. -/
theorem distinct {i j : Fin 5} (hij : i ≠ j) : ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- **(3) Counting.** The number of isomorphism classes of groups of order `8` is
exactly `5`, the GAP SmallGroups library count. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 8 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order8
