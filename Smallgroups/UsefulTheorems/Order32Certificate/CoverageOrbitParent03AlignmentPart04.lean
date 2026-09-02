/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart06
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03AlignmentPart03

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 3, orbit 3, alignment to GAP id 6. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP3OrbitGroup3 := CocycleGroup
  (orbitP3SelectedCocycle 3) (orbitP3SelectedCocycle_consistent 3)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP3GapEquiv3 :
    orbitP3OrbitGroup3 ≃* PCGroup smallGroup_32_6 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv6

end Smallgroups.UsefulTheorems.Order32Certificate
