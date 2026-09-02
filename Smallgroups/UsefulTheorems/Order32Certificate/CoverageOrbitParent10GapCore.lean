/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart04
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart05
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart06
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart07
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart08
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart09
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10AlignmentPart10
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP10GapIndex : Fin 10 → Fin 51 :=
  ![44, 20, 24, 22, 21, 25, 23, 35, 37, 36]
noncomputable def orbitP10SelectedGapEquiv : ∀ o : Fin 10,
    CocycleGroup (orbitP10SelectedCocycle o) (orbitP10SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP10GapIndex o)
  | 0 => orbitP10GapEquiv0
  | 1 => orbitP10GapEquiv1
  | 2 => orbitP10GapEquiv2
  | 3 => orbitP10GapEquiv3
  | 4 => orbitP10GapEquiv4
  | 5 => orbitP10GapEquiv5
  | 6 => orbitP10GapEquiv6
  | 7 => orbitP10GapEquiv7
  | 8 => orbitP10GapEquiv8
  | 9 => orbitP10GapEquiv9

end Smallgroups.UsefulTheorems.Order32Certificate
