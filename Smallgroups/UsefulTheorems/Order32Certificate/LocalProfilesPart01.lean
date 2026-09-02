/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesData
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart51

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel check of the local profile of `SmallGroup(32,1)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems
open Smallgroups.GAP

def order32LocalProfileValue1 : Multiset Order32LocalFeature :=
  ([(32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (32, 32, 0, 0), (48, 32, 2, 0), (48, 32, 2, 0), (48, 32, 2, 0), (48, 32, 2, 0), (48, 32, 2, 0), (48, 32, 2, 0), (48, 32, 2, 0), (48, 32, 2, 0), (56, 32, 2, 4), (56, 32, 2, 4), (56, 32, 2, 4), (56, 32, 2, 4), (60, 32, 2, 4), (60, 32, 2, 4), (62, 32, 2, 4), (63, 32, 2, 4)] : Multiset Order32LocalFeature)

set_option maxHeartbeats 8000000 in
-- Exhaustive finite count over the 32-element imported PC group.
theorem order32_local_profile_1 :
    order32LocalProfile (PCGroup smallGroup_32_1) =
      order32LocalProfileValue1 := by
  decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
