/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart07

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 3, orbit 6, alignment to GAP id 7. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP3OrbitGroup6 := CocycleGroup
  (orbitP3SelectedCocycle 6) (orbitP3SelectedCocycle_consistent 6)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP3GapEquiv6 :
    orbitP3OrbitGroup6 ≃* PCGroup smallGroup_32_7 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv7

end Smallgroups.UsefulTheorems.Order32Certificate
