/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart04

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 2, orbit 3, alignment to GAP id 4. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP2OrbitGroup3 := CocycleGroup
  (orbitP2SelectedCocycle 3) (orbitP2SelectedCocycle_consistent 3)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP2GapEquiv3 :
    orbitP2OrbitGroup3 ≃* PCGroup smallGroup_32_4 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv4

end Smallgroups.UsefulTheorems.Order32Certificate
