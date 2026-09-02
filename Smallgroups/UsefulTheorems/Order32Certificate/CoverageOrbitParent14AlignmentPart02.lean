/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.Parent14OrbitAlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14AlignmentPart01

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 14, orbit 1, alignment to GAP id 45. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP14OrbitGroup1 := CocycleGroup
  (orbitP14SelectedCocycle 1) (orbitP14SelectedCocycle_consistent 1)
set_option maxHeartbeats 8000000 in
-- Reuse the independently checked direct PC map from the parent-14 pilot.
noncomputable def orbitP14GapEquiv1 :
    orbitP14OrbitGroup1 ≃* PCGroup smallGroup_32_45 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    parent14OrbitGapEquiv1

end Smallgroups.UsefulTheorems.Order32Certificate
