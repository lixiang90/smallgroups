/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart01

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 1, orbit 1, alignment to GAP id 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP1OrbitGroup1 := CocycleGroup
  (orbitP1SelectedCocycle 1) (orbitP1SelectedCocycle_consistent 1)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP1GapEquiv1 :
    orbitP1OrbitGroup1 ≃* PCGroup smallGroup_32_1 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv1

end Smallgroups.UsefulTheorems.Order32Certificate
