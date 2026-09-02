/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart41
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08AlignmentPart04

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 9, orbit 0, alignment to GAP id 41. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP9OrbitGroup0 := CocycleGroup
  (orbitP9SelectedCocycle 0) (orbitP9SelectedCocycle_consistent 0)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP9GapEquiv0 :
    orbitP9OrbitGroup0 ≃* PCGroup smallGroup_32_41 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv41

end Smallgroups.UsefulTheorems.Order32Certificate
