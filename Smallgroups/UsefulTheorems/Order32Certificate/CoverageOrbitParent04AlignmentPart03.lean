/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart13
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04AlignmentPart02

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 4, orbit 2, alignment to GAP id 13. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP4OrbitGroup2 := CocycleGroup
  (orbitP4SelectedCocycle 2) (orbitP4SelectedCocycle_consistent 2)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP4GapEquiv2 :
    orbitP4OrbitGroup2 ≃* PCGroup smallGroup_32_13 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv13

end Smallgroups.UsefulTheorems.Order32Certificate
