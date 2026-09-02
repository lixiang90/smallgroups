/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08AlignmentPart04
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP8GapIndex : Fin 4 → Fin 51 :=
  ![39, 12, 8, 9]
noncomputable def orbitP8SelectedGapEquiv : ∀ o : Fin 4,
    CocycleGroup (orbitP8SelectedCocycle o) (orbitP8SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP8GapIndex o)
  | 0 => orbitP8GapEquiv0
  | 1 => orbitP8GapEquiv1
  | 2 => orbitP8GapEquiv2
  | 3 => orbitP8GapEquiv3

end Smallgroups.UsefulTheorems.Order32Certificate
