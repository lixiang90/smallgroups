/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart04
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart05
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart06
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart07
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart08
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart09
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13AlignmentPart10
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP13GapIndex : Fin 10 → Fin 51 :=
  ![47, 24, 27, 29, 30, 28, 23, 32, 25, 31]
noncomputable def orbitP13SelectedGapEquiv : ∀ o : Fin 10,
    CocycleGroup (orbitP13SelectedCocycle o) (orbitP13SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP13GapIndex o)
  | 0 => orbitP13GapEquiv0
  | 1 => orbitP13GapEquiv1
  | 2 => orbitP13GapEquiv2
  | 3 => orbitP13GapEquiv3
  | 4 => orbitP13GapEquiv4
  | 5 => orbitP13GapEquiv5
  | 6 => orbitP13GapEquiv6
  | 7 => orbitP13GapEquiv7
  | 8 => orbitP13GapEquiv8
  | 9 => orbitP13GapEquiv9

end Smallgroups.UsefulTheorems.Order32Certificate
