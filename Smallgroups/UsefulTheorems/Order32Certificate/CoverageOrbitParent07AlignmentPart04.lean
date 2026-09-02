/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart18
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07AlignmentPart03

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 7, orbit 3, alignment to GAP id 18. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP7OrbitGroup3 := CocycleGroup
  (orbitP7SelectedCocycle 3) (orbitP7SelectedCocycle_consistent 3)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP7GapEquiv3 :
    orbitP7OrbitGroup3 ≃* PCGroup smallGroup_32_18 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv18

end Smallgroups.UsefulTheorems.Order32Certificate
