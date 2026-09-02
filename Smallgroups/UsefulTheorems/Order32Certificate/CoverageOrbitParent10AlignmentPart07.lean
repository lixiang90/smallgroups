/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart24
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart06

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 10, orbit 6, alignment to GAP id 24. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP10OrbitGroup6 := CocycleGroup
  (orbitP10SelectedCocycle 6) (orbitP10SelectedCocycle_consistent 6)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP10GapEquiv6 :
    orbitP10OrbitGroup6 ≃* PCGroup smallGroup_32_24 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv24

end Smallgroups.UsefulTheorems.Order32Certificate
