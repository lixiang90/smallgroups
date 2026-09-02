/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart15
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04AlignmentPart05

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 4, orbit 5, alignment to GAP id 15. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP4OrbitGroup5 := CocycleGroup
  (orbitP4SelectedCocycle 5) (orbitP4SelectedCocycle_consistent 5)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP4GapEquiv5 :
    orbitP4OrbitGroup5 ≃* PCGroup smallGroup_32_15 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv15

end Smallgroups.UsefulTheorems.Order32Certificate
