/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart33

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 13, orbit 7, alignment to GAP id 33. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP13OrbitGroup7 := CocycleGroup
  (orbitP13SelectedCocycle 7) (orbitP13SelectedCocycle_consistent 7)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP13GapEquiv7 :
    orbitP13OrbitGroup7 ≃* PCGroup smallGroup_32_33 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv33

end Smallgroups.UsefulTheorems.Order32Certificate
