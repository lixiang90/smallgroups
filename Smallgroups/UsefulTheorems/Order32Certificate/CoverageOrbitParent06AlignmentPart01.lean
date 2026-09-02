/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart37
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Complete

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 6, orbit 0, alignment to GAP id 37. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP6OrbitGroup0 := CocycleGroup
  (orbitP6SelectedCocycle 0) (orbitP6SelectedCocycle_consistent 0)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP6GapEquiv0 :
    orbitP6OrbitGroup0 ≃* PCGroup smallGroup_32_37 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv37

end Smallgroups.UsefulTheorems.Order32Certificate
