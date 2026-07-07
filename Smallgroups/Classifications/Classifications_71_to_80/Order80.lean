/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order80.Classification

/-!
# Classification of groups of order 80

`80 = 2⁴ · 5`. There are exactly **52** isomorphism classes of groups of
order `80`, split by the Sylow dichotomy (`n₅ = 1` or `n₅ = 16`):

1. **`n₅ = 1` (51 classes).** The Sylow-`5` subgroup is normal and
   Schur–Zassenhaus gives `G ≅ C₅ ⋊[χ] K` with `K` one of the `14` groups of
   order `16`; classifying the characters `χ : K →* (ℤ/5)ˣ` up to `Aut K`
   yields `2+5+4+5+3+3+3+4+4+4+4+3+4+3 = 51` classes
   (`Smallgroups.UsefulTheorems.order80_normal_reps`).
2. **`n₅ = 16` (1 class).** The Sylow-`2` subgroup is normal,
   `G ≅ P ⋊[φ] C₅` with `|P| = 16` and `φ` nontrivial; only `P = (C₂)⁴`
   admits an order-`5` automorphism, and all nontrivial actions give the
   single group `(C₂)⁴ ⋊ C₅`
   (`Smallgroups.UsefulTheorems.order80_nonnormal_rep`).

This file re-exports the bundled result from
`Smallgroups.UsefulTheorems.Order80.Classification`.
-/

namespace Smallgroups.Classifications.Order80

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order 80 is isomorphic to one of the
52 representatives. -/
theorem classification (G : Type) [Group G] (h : Nat.card G = 80) :
    ∃ n : Fin 52, Nonempty (G ≃* order80_reps n) :=
  order80_classification G h

/-- **(2) Distinctness.** The 52 representatives are pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (order80_reps i ≃* order80_reps j) → i = j :=
  order80_isClassif.distinct

/-- **(3) Counting.** The 52 representatives are a complete, non-redundant list
of representatives of the groups of order 80. -/
theorem isClassif : IsClassif 80 order80_reps := order80_isClassif

/-- **The number of isomorphism classes of groups of order 80 is exactly
`52`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 80 rep) : k = 52 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order80
