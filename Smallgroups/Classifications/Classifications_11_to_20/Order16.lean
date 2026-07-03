/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.Counting

/-!
# Classification of groups of order 16

There are exactly **fourteen** isomorphism classes of groups of order `16`, following
Marcel Wild's "The Groups of Order Sixteen Made Easy" (AMM, 2005):

Abelian (five classes, by partitions of the exponent `4`):

* `Rep0 = (C₂)⁴`
* `Rep1 = C₈ × C₂`
* `Rep6 = C₁₆`
* `Rep7 = K₄ × C₄ = C₄ × C₂ × C₂`
* `Rep13 = C₄ × C₄`

Non-abelian, built as an extension of a normal `C₈` (six classes):

* `Rep2 = SD₁₆` (semidihedral)
* `Rep3 = C₈ ⋊₅ C₂` (modular)
* `Rep4 = D₁₆` (dihedral)
* `Rep5 = Q₁₆` (generalized quaternion)

Non-abelian, built as an extension of a normal `K₈ = C₄ × C₂` (the remaining four classes):

* `Rep8 = D₈ × C₂`
* `Rep9 = K₄ ⋊ C₄`
* `Rep10 = Q₈ ⋊ C₂`
* `Rep11 = Q₈ × C₂`
* `Rep12 = C₄ ⋊ C₄`

All of the mathematical content lives in `Smallgroups.UsefulTheorems.Order16_Wild`; this file
simply repackages the result under the project's per-order naming convention.

* `classification` — (1) exhaustiveness: every group of order `16` is isomorphic to one of the
  fourteen representatives.
* `distinct` — (2) distinctness: the fourteen representatives are pairwise non-isomorphic.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there are exactly fourteen isomorphism classes.
-/

namespace Smallgroups.Classifications.Order16

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- The fourteen isomorphism classes of groups of order `16` (Wild numbering). -/
abbrev Rep : Fin 14 → Type := order16_wild_reps

noncomputable instance instGroupRep (i : Fin 14) : Group (Rep i) :=
  instGroupOrder16WildReps i

/-- `Rep 0 = (C₂)⁴`. -/
abbrev Rep0 : Type := order16_wild_G0
/-- `Rep 1 = C₈ × C₂`. -/
abbrev Rep1 : Type := order16_wild_G1
/-- `Rep 2 = SD₁₆` (semidihedral). -/
abbrev Rep2 : Type := order16_wild_G2
/-- `Rep 3 = C₈ ⋊₅ C₂` (modular group of order `16`). -/
abbrev Rep3 : Type := order16_wild_G3
/-- `Rep 4 = D₁₆` (dihedral). -/
abbrev Rep4 : Type := order16_wild_G4
/-- `Rep 5 = Q₁₆` (generalized quaternion). -/
abbrev Rep5 : Type := order16_wild_G5
/-- `Rep 6 = C₁₆` (cyclic). -/
abbrev Rep6 : Type := order16_wild_G6
/-- `Rep 7 = K₄ × C₄`. -/
abbrev Rep7 : Type := order16_wild_G7
/-- `Rep 8 = D₈ × C₂`. -/
abbrev Rep8 : Type := order16_wild_G8
/-- `Rep 9 = K₄ ⋊ C₄`. -/
abbrev Rep9 : Type := order16_wild_G9
/-- `Rep 10 = Q₈ ⋊ C₂`. -/
abbrev Rep10 : Type := order16_wild_G10
/-- `Rep 11 = Q₈ × C₂`. -/
abbrev Rep11 : Type := order16_wild_G11
/-- `Rep 12 = C₄ ⋊ C₄`. -/
abbrev Rep12 : Type := order16_wild_G12
/-- `Rep 13 = C₄ × C₄`. -/
abbrev Rep13 : Type := order16_wild_G13

/-- Each of the fourteen representatives has order `16`. -/
theorem card_Rep (i : Fin 14) : Nat.card (Rep i) = 16 := card_order16_wild_reps i

/-- **(1) Exhaustiveness.** Every group of order `16` is isomorphic to one of the fourteen
representatives. -/
theorem classification (h : Nat.card G = 16) : ∃ i : Fin 14, Nonempty (G ≃* Rep i) :=
  order16_wild_classification h

/-- **(2) Distinctness.** The fourteen representatives are pairwise non-isomorphic. -/
theorem distinct {i j : Fin 14} (h : Nonempty (Rep i ≃* Rep j)) : i = j :=
  order16_wild_distinct h

/-- **(3) Counting.** The fourteen representatives form a complete, non-redundant list of
representatives of the groups of order `16` — assembled from exhaustiveness (`classification`)
and distinctness (`distinct`). -/
theorem isClassif : IsClassif 16 Rep := order16_wild_isClassif

/-- **The number of isomorphism classes of groups of order `16` is exactly `14`:** any complete
list of pairwise non-isomorphic representatives has length `14`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 16 rep) : k = 14 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order16
