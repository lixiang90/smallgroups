/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03AlignmentPart04
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03AlignmentPart05
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03AlignmentPart06
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03AlignmentPart07
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03AlignmentPart08
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03AlignmentPart09
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP3GapIndex : Fin 9 → Fin 51 :=
  ![21, 8, 10, 5, 1, 9, 6, 4, 7]
noncomputable def orbitP3SelectedGapEquiv : ∀ o : Fin 9,
    CocycleGroup (orbitP3SelectedCocycle o) (orbitP3SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP3GapIndex o)
  | 0 => orbitP3GapEquiv0
  | 1 => orbitP3GapEquiv1
  | 2 => orbitP3GapEquiv2
  | 3 => orbitP3GapEquiv3
  | 4 => orbitP3GapEquiv4
  | 5 => orbitP3GapEquiv5
  | 6 => orbitP3GapEquiv6
  | 7 => orbitP3GapEquiv7
  | 8 => orbitP3GapEquiv8

end Smallgroups.UsefulTheorems.Order32Certificate
