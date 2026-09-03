/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart30

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 8, alignment to GAP id 30. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup8 := CocycleGroup
  (orbitP11SelectedCocycle 8) (orbitP11SelectedCocycle_consistent 8)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP11GapEquiv8 :
    orbitP11OrbitGroup8 ≃* PCGroup smallGroup_32_30 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv30

end Smallgroups.UsefulTheorems.Order32Certificate
