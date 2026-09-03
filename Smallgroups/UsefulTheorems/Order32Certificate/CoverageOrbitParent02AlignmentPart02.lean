/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart03

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 2, orbit 1, alignment to GAP id 3. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP2OrbitGroup1 := CocycleGroup
  (orbitP2SelectedCocycle 1) (orbitP2SelectedCocycle_consistent 1)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP2GapEquiv1 :
    orbitP2OrbitGroup1 ≃* PCGroup smallGroup_32_3 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv3

end Smallgroups.UsefulTheorems.Order32Certificate
