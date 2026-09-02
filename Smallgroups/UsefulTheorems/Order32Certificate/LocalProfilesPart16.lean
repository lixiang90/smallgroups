/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesData
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart16
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart15

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel check of the local profile of `SmallGroup(32,16)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems
open Smallgroups.GAP

def order32LocalProfileValue16 : Multiset Order32LocalFeature :=
  ([(48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (48, 32, 0, 0), (56, 32, 0, 0), (56, 32, 0, 0), (56, 32, 0, 0), (56, 32, 0, 0), (56, 32, 4, 0), (56, 32, 4, 0), (56, 32, 4, 0), (56, 32, 4, 0), (60, 32, 0, 0), (60, 32, 0, 0), (60, 32, 4, 8), (60, 32, 4, 8), (62, 32, 0, 0), (62, 32, 0, 0), (62, 32, 4, 8), (63, 32, 4, 8)] : Multiset Order32LocalFeature)

set_option maxHeartbeats 8000000 in
-- Exhaustive finite count over the 32-element imported PC group.
theorem order32_local_profile_16 :
    order32LocalProfile (PCGroup smallGroup_32_16) =
      order32LocalProfileValue16 := by
  decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
