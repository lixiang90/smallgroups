/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02AlignmentPart02

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 2, orbit 2, alignment to GAP id 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP2OrbitGroup2 := CocycleGroup
  (orbitP2SelectedCocycle 2) (orbitP2SelectedCocycle_consistent 2)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP2GapEquiv2 :
    orbitP2OrbitGroup2 ≃* PCGroup smallGroup_32_2 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv2

end Smallgroups.UsefulTheorems.Order32Certificate
