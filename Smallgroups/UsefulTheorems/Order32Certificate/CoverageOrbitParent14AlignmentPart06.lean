/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.Parent14OrbitAlignmentPart06
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14AlignmentPart05

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 14, orbit 5, alignment to GAP id 49. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP14OrbitGroup5 := CocycleGroup
  (orbitP14SelectedCocycle 5) (orbitP14SelectedCocycle_consistent 5)
set_option maxHeartbeats 8000000 in
-- Reuse the independently checked direct PC map from the parent-14 pilot.
noncomputable def orbitP14GapEquiv5 :
    orbitP14OrbitGroup5 ≃* PCGroup smallGroup_32_49 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    parent14OrbitGapEquiv5

end Smallgroups.UsefulTheorems.Order32Certificate
