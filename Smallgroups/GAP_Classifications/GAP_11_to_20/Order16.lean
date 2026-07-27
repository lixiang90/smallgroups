/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.SmallGroup
import Smallgroups.GAP.Polycyclic.Imported.Order16Match
import Smallgroups.Classifications.Classifications_11_to_20.Order16

/-!
# GAP-numbered classification of groups of order 16

The fourteen groups of order `16`, in the GAP SmallGroups library numbering, are

`C₁₆, C₄×C₄, (C₄×C₂)⋊C₂, C₄⋊C₄, C₈×C₂, C₈⋊₅C₂, D₁₆, QD₁₆, Q₁₆, C₄×C₂×C₂, C₂×D₈,`
`C₂×Q₈, (C₄×C₂)⋊C₂` (a second group of this shape), `(C₂)⁴`.

The representatives are the imported pc groups `smallGroup 16 j`
(`GAP/SmallGroup.lean`); the isomorphisms to the project's existing order-`16`
representatives (`Order16_Wild`) are certified in
`Polycyclic/Imported/Order16Match.lean`, via the index permutation `perm16`
(`SmallGroup(16, j) ≅ G_{perm16(j)}`).

* `classification` — (1) exhaustiveness: every group of order `16` is isomorphic to
  `SmallGroup(16, j)` for some `j`.
* `distinct` — (2) distinctness: the `SmallGroup(16, j)` are pairwise non-isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: exactly fourteen isomorphism
  classes.
-/

namespace Smallgroups.GAP_Classifications.Order16

open Smallgroups.GAP Smallgroups.UsefulTheorems


/-- The GAP-numbered representatives of order `16`: `SmallGroup(16, j)`,
`j = 1, …, 14`. -/
abbrev gapRep : Fin 14 → Type :=
  rep14 (smallGroup 16 1) (smallGroup 16 2) (smallGroup 16 3) (smallGroup 16 4)
    (smallGroup 16 5) (smallGroup 16 6) (smallGroup 16 7) (smallGroup 16 8)
    (smallGroup 16 9) (smallGroup 16 10) (smallGroup 16 11) (smallGroup 16 12)
    (smallGroup 16 13) (smallGroup 16 14)

/-- The permutation aligning the existing order-`16` list (`order16_wild_reps`,
`G₀ … G₁₃`) with the GAP numbering: `SmallGroup(16, j) ≅ G_{perm16(j)}`. -/
private noncomputable def perm16 : Fin 14 ≃ Fin 14 :=
  Equiv.ofBijective
    (fun i => match i with
      | 0 => ⟨6, by decide⟩
      | 1 => ⟨13, by decide⟩
      | 2 => ⟨9, by decide⟩
      | 3 => ⟨12, by decide⟩
      | 4 => ⟨1, by decide⟩
      | 5 => ⟨3, by decide⟩
      | 6 => ⟨4, by decide⟩
      | 7 => ⟨2, by decide⟩
      | 8 => ⟨5, by decide⟩
      | 9 => ⟨7, by decide⟩
      | 10 => ⟨8, by decide⟩
      | 11 => ⟨11, by decide⟩
      | 12 => ⟨10, by decide⟩
      | 13 => ⟨0, by decide⟩)
    (by decide)

/-- The GAP representatives are isomorphic, index by index, to the permuted existing
list. -/
private noncomputable def gapEquivs : ∀ i, gapRep i ≃* order16_wild_reps (perm16 i)
  | 0 => order16_1_equiv
  | 1 => order16_2_equiv
  | 2 => order16_3_equiv
  | 3 => order16_4_equiv
  | 4 => order16_5_equiv
  | 5 => order16_6_equiv
  | 6 => order16_7_equiv
  | 7 => order16_8_equiv
  | 8 => order16_9_equiv
  | 9 => order16_10_equiv
  | 10 => order16_11_equiv
  | 11 => order16_12_equiv
  | 12 => order16_13_equiv
  | 13 => order16_14_equiv

/-- **(1)+(2)+(3).** The GAP-numbered list `[SmallGroup(16, 1), …, SmallGroup(16, 14)]`
is a complete, non-redundant representative list of the groups of order `16`. -/
theorem isClassif : IsClassif 16 gapRep :=
  IsClassif.of_equivs
    (IsClassif.of_perm Smallgroups.Classifications.Order16.isClassif perm16) gapEquivs

/-- **(1) Exhaustiveness.** Every group of order `16` is isomorphic to
`SmallGroup(16, j)` for some `j`. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 16) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  isClassif.complete G h

/-- **(2) Distinctness.** The `SmallGroup(16, j)` are pairwise non-isomorphic. -/
theorem distinct {i j : Fin 14} (hij : i ≠ j) : ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- **(3) Counting.** The number of isomorphism classes of groups of order `16` is
exactly `14`, the GAP SmallGroups library count. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 16 rep) : k = 14 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order16
