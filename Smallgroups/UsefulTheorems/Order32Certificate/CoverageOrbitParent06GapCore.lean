/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06AlignmentPart04
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP6GapIndex : Fin 4 → Fin 51 :=
  ![36, 3, 4, 11]
noncomputable def orbitP6SelectedGapEquiv : ∀ o : Fin 4,
    CocycleGroup (orbitP6SelectedCocycle o) (orbitP6SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP6GapIndex o)
  | 0 => orbitP6GapEquiv0
  | 1 => orbitP6GapEquiv1
  | 2 => orbitP6GapEquiv2
  | 3 => orbitP6GapEquiv3

end Smallgroups.UsefulTheorems.Order32Certificate
