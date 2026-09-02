/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesData
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart19
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart18

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel check of the local profile of `SmallGroup(32,19)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems
open Smallgroups.GAP

def order32LocalProfileValue19 : Multiset Order32LocalFeature :=
  ([(48, 16, 0, 0), (48, 16, 0, 0), (48, 16, 0, 0), (48, 16, 0, 0), (48, 16, 0, 0), (48, 16, 0, 0), (48, 16, 0, 0), (48, 16, 0, 0), (56, 16, 2, 0), (56, 16, 2, 0), (56, 16, 2, 0), (56, 16, 2, 0), (60, 4, 0, 0), (60, 4, 0, 0), (60, 4, 0, 0), (60, 4, 0, 0), (60, 4, 0, 0), (60, 4, 0, 0), (60, 4, 0, 0), (60, 4, 0, 0), (60, 16, 2, 4), (60, 16, 2, 4), (62, 4, 0, 0), (62, 4, 0, 0), (62, 4, 0, 0), (62, 4, 0, 0), (62, 4, 0, 0), (62, 4, 0, 0), (62, 4, 0, 0), (62, 4, 0, 0), (62, 32, 10, 4), (63, 32, 10, 20)] : Multiset Order32LocalFeature)

set_option maxHeartbeats 8000000 in
-- Exhaustive finite count over the 32-element imported PC group.
theorem order32_local_profile_19 :
    order32LocalProfile (PCGroup smallGroup_32_19) =
      order32LocalProfileValue19 := by
  decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
