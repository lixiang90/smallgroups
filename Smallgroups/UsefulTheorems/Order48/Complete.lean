/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.Classification
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeRMComplete
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeRNComplete
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeROComplete

/-!
# Complete classification of groups of order 48

This file discharges the three residual cocycle hypotheses and packages the
52 structural representatives as an unconditional classification.
-/

namespace Smallgroups.UsefulTheorems

theorem order48_complete
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 48) :
    ∃ i, Nonempty (G ≃* order48_all_reps i) :=
  order48_complete_of_cocycle_exhaustive hG
    order48_RM_cocycle_exhaustive order48_RN_cocycle_exhaustive
    order48_RO_cocycle_exhaustive

/-- The 52 structural representatives form a classification of groups of
order 48.  Alignment with GAP numbering is intentionally deferred. -/
theorem order48_isClassif : IsClassif 48 order48_all_reps_fin :=
  order48_isClassif_of_cocycle_exhaustive
    order48_RM_cocycle_exhaustive order48_RN_cocycle_exhaustive
    order48_RO_cocycle_exhaustive

end Smallgroups.UsefulTheorems
