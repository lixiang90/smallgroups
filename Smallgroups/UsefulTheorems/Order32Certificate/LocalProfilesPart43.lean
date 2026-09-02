/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesData
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart43
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart42

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel check of the local profile of `SmallGroup(32,43)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems
open Smallgroups.GAP

def order32LocalProfileValue43 : Multiset Order32LocalFeature :=
  ([(56, 8, 0, 0), (56, 8, 0, 0), (56, 8, 0, 0), (56, 8, 0, 0), (56, 8, 0, 0), (56, 8, 0, 0), (56, 8, 0, 0), (56, 8, 0, 0), (60, 8, 0, 0), (60, 8, 0, 0), (60, 8, 0, 0), (60, 8, 0, 0), (60, 16, 0, 0), (60, 16, 0, 0), (60, 16, 4, 0), (60, 16, 4, 0), (62, 8, 0, 0), (62, 8, 0, 0), (62, 8, 0, 0), (62, 8, 0, 0), (62, 8, 0, 0), (62, 8, 0, 0), (62, 8, 0, 0), (62, 8, 0, 0), (62, 8, 0, 0), (62, 8, 0, 0), (62, 8, 0, 0), (62, 8, 0, 0), (62, 16, 0, 0), (62, 16, 0, 0), (62, 32, 8, 8), (63, 32, 16, 24)] : Multiset Order32LocalFeature)

set_option maxHeartbeats 8000000 in
-- Exhaustive finite count over the 32-element imported PC group.
theorem order32_local_profile_43 :
    order32LocalProfile (PCGroup smallGroup_32_43) =
      order32LocalProfileValue43 := by
  decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
