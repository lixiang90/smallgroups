/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionClassifiers

namespace Smallgroups.UsefulTheorems

/-! Test: Fintype of MulAut G₈ -/

section Test

noncomputable instance instFintypeMulAutG8 : Fintype (MulAut order16_wild_G8) := inferInstance

noncomputable instance instFintypeMulAutG10 : Fintype (MulAut order16_wild_G10) := inferInstance

noncomputable instance instFintypeMulAutG11 : Fintype (MulAut order16_wild_G11) := inferInstance

set_option maxHeartbeats 1600000 in
theorem card_MulAut_G8 : Fintype.card (MulAut order16_wild_G8) = 8 := by decide +kernel


end Test

end Smallgroups.UsefulTheorems
