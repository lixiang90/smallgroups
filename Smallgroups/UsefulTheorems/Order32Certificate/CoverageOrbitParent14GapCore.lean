/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14AlignmentPart04
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14AlignmentPart05
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14AlignmentPart06
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14AlignmentPart07
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP14GapIndex : Fin 7 → Fin 51 :=
  ![50, 44, 45, 46, 47, 48, 49]
noncomputable def orbitP14SelectedGapEquiv : ∀ o : Fin 7,
    CocycleGroup (orbitP14SelectedCocycle o) (orbitP14SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP14GapIndex o)
  | 0 => orbitP14GapEquiv0
  | 1 => orbitP14GapEquiv1
  | 2 => orbitP14GapEquiv2
  | 3 => orbitP14GapEquiv3
  | 4 => orbitP14GapEquiv4
  | 5 => orbitP14GapEquiv5
  | 6 => orbitP14GapEquiv6

end Smallgroups.UsefulTheorems.Order32Certificate
