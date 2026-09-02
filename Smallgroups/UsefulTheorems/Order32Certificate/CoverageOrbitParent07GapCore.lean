/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07AlignmentPart04
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07AlignmentPart05
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07AlignmentPart06
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP7GapIndex : Fin 6 → Fin 51 :=
  ![38, 13, 8, 17, 19, 18]
noncomputable def orbitP7SelectedGapEquiv : ∀ o : Fin 6,
    CocycleGroup (orbitP7SelectedCocycle o) (orbitP7SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP7GapIndex o)
  | 0 => orbitP7GapEquiv0
  | 1 => orbitP7GapEquiv1
  | 2 => orbitP7GapEquiv2
  | 3 => orbitP7GapEquiv3
  | 4 => orbitP7GapEquiv4
  | 5 => orbitP7GapEquiv5

end Smallgroups.UsefulTheorems.Order32Certificate
