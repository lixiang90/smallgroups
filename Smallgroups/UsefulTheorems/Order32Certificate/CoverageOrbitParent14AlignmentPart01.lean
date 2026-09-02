/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.Parent14OrbitAlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart10

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 14, orbit 0, alignment to GAP id 51. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP14OrbitGroup0 := CocycleGroup
  (orbitP14SelectedCocycle 0) (orbitP14SelectedCocycle_consistent 0)
set_option maxHeartbeats 8000000 in
-- Reuse the independently checked direct PC map from the parent-14 pilot.
noncomputable def orbitP14GapEquiv0 :
    orbitP14OrbitGroup0 ≃* PCGroup smallGroup_32_51 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    parent14OrbitGapEquiv0

end Smallgroups.UsefulTheorems.Order32Certificate
