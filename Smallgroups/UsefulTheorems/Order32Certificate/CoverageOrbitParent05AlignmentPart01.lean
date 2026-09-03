/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart36

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 5, orbit 0, alignment to GAP id 36. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP5OrbitGroup0 := CocycleGroup
  (orbitP5SelectedCocycle 0) (orbitP5SelectedCocycle_consistent 0)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP5GapEquiv0 :
    orbitP5OrbitGroup0 ≃* PCGroup smallGroup_32_36 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv36

end Smallgroups.UsefulTheorems.Order32Certificate
