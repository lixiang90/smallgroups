/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12AlignmentPart04
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12AlignmentPart05
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12AlignmentPart06
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP12GapIndex : Fin 6 → Fin 51 :=
  ![46, 25, 34, 28, 22, 31]
noncomputable def orbitP12SelectedGapEquiv : ∀ o : Fin 6,
    CocycleGroup (orbitP12SelectedCocycle o) (orbitP12SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP12GapIndex o)
  | 0 => orbitP12GapEquiv0
  | 1 => orbitP12GapEquiv1
  | 2 => orbitP12GapEquiv2
  | 3 => orbitP12GapEquiv3
  | 4 => orbitP12GapEquiv4
  | 5 => orbitP12GapEquiv5

end Smallgroups.UsefulTheorems.Order32Certificate
