/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart14

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 4, orbit 1, alignment to GAP id 14. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP4OrbitGroup1 := CocycleGroup
  (orbitP4SelectedCocycle 1) (orbitP4SelectedCocycle_consistent 1)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP4GapEquiv1 :
    orbitP4OrbitGroup1 ≃* PCGroup smallGroup_32_14 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv14

end Smallgroups.UsefulTheorems.Order32Certificate
