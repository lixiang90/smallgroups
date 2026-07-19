/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.DistinctnessAll

/-!
# Classification of groups of order 72

`72 = 2³ · 3²`. There are exactly **50** isomorphism classes of groups of
order `72`, split by the Sylow trichotomy:

1. **Normal Sylow `3` (`n₃ = 1`, 42 classes).** `G ≅ K ⋊ H` with `K` one of the two
   order-`9` groups and `H` one of the five order-`8` groups acting on it; the ten
   direct products are shared with the Sylow-`2`-normal branch
   (`order72Sylow3NormalSolvedAllCases`).
2. **Normal Sylow `2` (`n₂ = 1`, 14 classes).** `G ≅ H ⋊ K` with `|H| = 8` normal;
   besides the ten direct products there are four nontrivial actions
   (`order72Sylow2NormalRepCases`).
3. **Residual (`n₃ = 4 ∧ n₂ ≠ 1`, 4 classes).** `S₃ × A₄`, `C₃ × S₄`, `C₃ ⋊ S₄`
   (sign action), and the non-split `C₃.S₄` (Goursat fiber product `D₉ ×_{S₃} S₄`).

The reduction of the residual branch to its kernel/image analysis is proved
(`order72ResidualKernelCases`); the conversion of that endpoint into the four explicit
residual representatives is currently assumed by the axiom
`order72_residual_kernel_cases_to_repCases` (the single open assumption of this
classification, see `Smallgroups.UsefulTheorems.Order72.Classification`).

Distinctness of the fifty representatives is proved by the invariant tables in
`DistinctnessDirect`/`DistinctnessC9`/`DistinctnessE9`/`DistinctnessSylow2`/
`DistinctnessResidual` plus the cross-branch separation in `DistinctnessAll`.

This file re-exports the bundled result from
`Smallgroups.UsefulTheorems.Order72.DistinctnessAll`.
-/

namespace Smallgroups.Classifications.Order72

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order 72 is isomorphic to one of the
50 representatives. -/
theorem classification (G : Type) [Group G] (h : Nat.card G = 72) :
    ∃ n : Fin 50, Nonempty (G ≃* order72_reps n) :=
  order72_complete G h

/-- **(2) Distinctness.** The 50 representatives are pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (order72_reps i ≃* order72_reps j) → i = j :=
  order72_isClassif.distinct

/-- **(3) Counting.** The 50 representatives are a complete, non-redundant list
of representatives of the groups of order 72. -/
theorem isClassif : IsClassif 72 order72_reps := order72_isClassif

/-- **The number of isomorphism classes of groups of order 72 is exactly
`50`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 72 rep) : k = 50 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order72
