/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart40

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 8, orbit 0, alignment to GAP id 40. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP8OrbitGroup0 := CocycleGroup
  (orbitP8SelectedCocycle 0) (orbitP8SelectedCocycle_consistent 0)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP8GapEquiv0 :
    orbitP8OrbitGroup0 ≃* PCGroup smallGroup_32_40 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv40

end Smallgroups.UsefulTheorems.Order32Certificate
