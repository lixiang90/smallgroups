/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesData
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart50
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart49

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel check of the local profile of `SmallGroup(32,50)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems
open Smallgroups.GAP

def order32LocalProfileValue50 : Multiset Order32LocalFeature :=
  ([(60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (62, 16, 0, 0), (62, 16, 0, 0), (62, 16, 0, 0), (62, 16, 0, 0), (62, 16, 0, 0), (62, 16, 0, 0), (62, 16, 0, 0), (62, 16, 0, 0), (62, 16, 0, 0), (62, 16, 0, 0), (62, 32, 20, 0), (63, 32, 12, 32)] : Multiset Order32LocalFeature)

set_option maxHeartbeats 8000000 in
-- Exhaustive finite count over the 32-element imported PC group.
theorem order32_local_profile_50 :
    order32LocalProfile (PCGroup smallGroup_32_50) =
      order32LocalProfileValue50 := by
  decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
