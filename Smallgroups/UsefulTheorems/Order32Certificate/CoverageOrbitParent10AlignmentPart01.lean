/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart45
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Complete

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 10, orbit 0, alignment to GAP id 45. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP10OrbitGroup0 := CocycleGroup
  (orbitP10SelectedCocycle 0) (orbitP10SelectedCocycle_consistent 0)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP10GapEquiv0 :
    orbitP10OrbitGroup0 ≃* PCGroup smallGroup_32_45 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv45

end Smallgroups.UsefulTheorems.Order32Certificate
