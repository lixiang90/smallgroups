/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart26
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart05

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 10, orbit 5, alignment to GAP id 26. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP10OrbitGroup5 := CocycleGroup
  (orbitP10SelectedCocycle 5) (orbitP10SelectedCocycle_consistent 5)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP10GapEquiv5 :
    orbitP10OrbitGroup5 ≃* PCGroup smallGroup_32_26 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv26

end Smallgroups.UsefulTheorems.Order32Certificate
