/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart47
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Complete

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 12, orbit 0, alignment to GAP id 47. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP12OrbitGroup0 := CocycleGroup
  (orbitP12SelectedCocycle 0) (orbitP12SelectedCocycle_consistent 0)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP12GapEquiv0 :
    orbitP12OrbitGroup0 ≃* PCGroup smallGroup_32_47 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv47

end Smallgroups.UsefulTheorems.Order32Certificate
