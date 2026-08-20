/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeG0
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeG7
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeG8
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeG10
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeG11

/-!
# Completion of the `RM` residual branch

This module assembles the five possible order-`16` kernels and closes the
`(C₂)^3 ⋊ C₃` cocycle branch.
-/

namespace Smallgroups.UsefulTheorems

theorem order48_RM_wild_action_complete : Order48RMWildActionComplete :=
  order48_RM_wild_action_complete_of_kernel_cases
    order48_G0_action_complete order48_G7_action_complete
    order48_G8_action_complete order48_G10_action_complete
    order48_G11_action_complete

theorem order48_RM_cocycle_exhaustive :
    Order48FourCocycleExhaustive order24_RM :=
  order48_RM_cocycle_exhaustive_of_wild_action_complete
    order48_RM_wild_action_complete

end Smallgroups.UsefulTheorems
