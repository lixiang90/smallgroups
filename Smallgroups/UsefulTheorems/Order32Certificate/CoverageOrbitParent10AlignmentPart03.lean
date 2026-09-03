/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart25

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 10, orbit 2, alignment to GAP id 25. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP10OrbitGroup2 := CocycleGroup
  (orbitP10SelectedCocycle 2) (orbitP10SelectedCocycle_consistent 2)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP10GapEquiv2 :
    orbitP10OrbitGroup2 ≃* PCGroup smallGroup_32_25 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv25

end Smallgroups.UsefulTheorems.Order32Certificate
