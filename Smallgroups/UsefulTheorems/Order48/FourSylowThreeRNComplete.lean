/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeG11
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeG12

/-!
# Completion of the `RN` residual branch
-/

namespace Smallgroups.UsefulTheorems

theorem order48_RN_wild_action_complete : Order48RNWildActionComplete :=
  order48_RN_wild_action_complete_of_kernel_cases
    order48_G11_action_complete order48_G12_action_complete

theorem order48_RN_cocycle_exhaustive :
    Order48FourCocycleExhaustive order24_RN :=
  order48_RN_cocycle_exhaustive_of_wild_action_complete
    order48_RN_wild_action_complete

end Smallgroups.UsefulTheorems
