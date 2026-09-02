/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.Parent14OrbitAlignmentPart04
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14AlignmentPart03

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 14, orbit 3, alignment to GAP id 47. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP14OrbitGroup3 := CocycleGroup
  (orbitP14SelectedCocycle 3) (orbitP14SelectedCocycle_consistent 3)
set_option maxHeartbeats 8000000 in
-- Reuse the independently checked direct PC map from the parent-14 pilot.
noncomputable def orbitP14GapEquiv3 :
    orbitP14OrbitGroup3 ≃* PCGroup smallGroup_32_47 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    parent14OrbitGapEquiv3

end Smallgroups.UsefulTheorems.Order32Certificate
