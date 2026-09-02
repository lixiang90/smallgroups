/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart29
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart09

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent 11, orbit 9, alignment to GAP id 29. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

abbrev orbitP11OrbitGroup9 := CocycleGroup
  (orbitP11SelectedCocycle 9) (orbitP11SelectedCocycle_consistent 9)
set_option maxHeartbeats 8000000 in
-- Kernel check that this selected orbit is the canonical generated representative.
noncomputable def orbitP11GapEquiv9 :
    orbitP11OrbitGroup9 ≃* PCGroup smallGroup_32_29 :=
  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans
    generatedGapEquiv29

end Smallgroups.UsefulTheorems.Order32Certificate
