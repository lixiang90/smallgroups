/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart20

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 7, orbit 4, alignment to GAP id 20. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP7OrbitGroup4 := CocycleGroup
  (orbitP7SelectedCocycle 4) (orbitP7SelectedCocycle_consistent 4)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP7GapEquiv4 :
    orbitP7OrbitGroup4 ≃* PCGroup smallGroup_32_20 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv20

end Smallgroups.UsefulTheorems.Order32Certificate
