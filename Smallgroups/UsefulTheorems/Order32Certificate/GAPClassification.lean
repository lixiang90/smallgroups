/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32.Common
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitScalableAll
import Smallgroups.UsefulTheorems.Order32Certificate.ParentWildAlignment
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesIdentity

/-!
# Classification of groups of order 32 in GAP SmallGroups order

The central-reduction theorem first presents an arbitrary group of order 32 as a central
`ZMod 2` extension of one of the fourteen existing Wild order-16 representatives.  The
checked table alignment transports that extension to the corresponding generated table,
where the cohomology/orbit certificates place it in `smallGroup32`.  Distinctness follows
from the independently checked local-profile invariant.
-/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP
open Smallgroups.UsefulTheorems.GF2Certificate

/-- Every group of order 32 is isomorphic to a GAP-numbered representative. -/
theorem order32_gap_classification (G : Type*) [Group G] [Finite G]
    (hG : Nat.card G = 32) :
    ∃ j : Fin 51, Nonempty (G ≃* smallGroup32 j) := by
  obtain ⟨i, f, hf, ⟨eG⟩⟩ := order32_central_reduction hG
  let p : Fin 14 := wildParentGapIndex i
  let α : Order16Table.Q (order16ParentTable p) ≃* order16_wild_reps i := by
    simpa [p] using wildParentTableEquiv i
  let g : Order16Table.Q (order16ParentTable p) →
      Order16Table.Q (order16ParentTable p) → F2 := fun a b => f (α a) (α b)
  let hg : IsCentralCocycle g := hf.comp α.toMonoidHom
  obtain ⟨j, ⟨etable⟩⟩ := order16ParentTable_cocycle_gap_complete p g hg
  refine ⟨j, ⟨eG.trans ?_⟩⟩
  exact (CocycleGroup.congrRight hf α).symm.trans etable

/-- The 51 GAP representatives are pairwise non-isomorphic. -/
theorem smallGroup32_pairwise_noniso : PairwiseNonMulEquiv smallGroup32 := by
  rintro i j ⟨e⟩
  apply order32LocalProfileTable_injective
  rw [← order32_local_profile_spec i, ← order32_local_profile_spec j]
  exact order32LocalProfile_eq_of_mulEquiv e

/-- The GAP-numbered family is a complete, irredundant classification of order 32. -/
theorem smallGroup32_isClassif : IsClassif 32 smallGroup32 where
  card := card_smallGroup32
  complete G _ hG := by
    haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
    exact order32_gap_classification G hG
  distinct := smallGroup32_pairwise_noniso

/-- Any complete nonredundant classification of order 32 has exactly 51 entries. -/
theorem numIsoClasses_order32_eq {k : ℕ} {rep : Fin k → Type}
    [∀ i, Group (rep i)] (h : IsClassif 32 rep) : k = 51 :=
  (smallGroup32_isClassif.card_unique h).symm

end Smallgroups.UsefulTheorems.Order32Certificate
