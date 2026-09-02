/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart17
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05AlignmentPart05

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 5, orbit 5, alignment to GAP id 17. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP5OrbitGroup5 := CocycleGroup
  (orbitP5SelectedCocycle 5) (orbitP5SelectedCocycle_consistent 5)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP5GapEquiv5 :
    orbitP5OrbitGroup5 ≃* PCGroup smallGroup_32_17 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv17

end Smallgroups.UsefulTheorems.Order32Certificate
