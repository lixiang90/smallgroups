/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart44
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart15

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 15, alignment to GAP id 44. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup15 := CocycleGroup
  (orbitP11SelectedCocycle 15) (orbitP11SelectedCocycle_consistent 15)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP11GapEquiv15 :
    orbitP11OrbitGroup15 ≃* PCGroup smallGroup_32_44 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv44

end Smallgroups.UsefulTheorems.Order32Certificate
