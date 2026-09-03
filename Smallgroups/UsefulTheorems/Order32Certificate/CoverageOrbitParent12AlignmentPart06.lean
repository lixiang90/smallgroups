/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart32

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 12, orbit 5, alignment to GAP id 32. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP12OrbitGroup5 := CocycleGroup
  (orbitP12SelectedCocycle 5) (orbitP12SelectedCocycle_consistent 5)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP12GapEquiv5 :
    orbitP12OrbitGroup5 ≃* PCGroup smallGroup_32_32 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv32

end Smallgroups.UsefulTheorems.Order32Certificate
