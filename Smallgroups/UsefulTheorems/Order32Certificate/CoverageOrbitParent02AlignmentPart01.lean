/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart21
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01AlignmentPart02

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 2, orbit 0, alignment to GAP id 21. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP2OrbitGroup0 := CocycleGroup
  (orbitP2SelectedCocycle 0) (orbitP2SelectedCocycle_consistent 0)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP2GapEquiv0 :
    orbitP2OrbitGroup0 ≃* PCGroup smallGroup_32_21 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv21

end Smallgroups.UsefulTheorems.Order32Certificate
