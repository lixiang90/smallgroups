/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05AlignmentPart04
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05AlignmentPart05
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05AlignmentPart06
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP5GapIndex : Fin 6 → Fin 51 :=
  ![35, 2, 4, 11, 15, 16]
noncomputable def orbitP5SelectedGapEquiv : ∀ o : Fin 6,
    CocycleGroup (orbitP5SelectedCocycle o) (orbitP5SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP5GapIndex o)
  | 0 => orbitP5GapEquiv0
  | 1 => orbitP5GapEquiv1
  | 2 => orbitP5GapEquiv2
  | 3 => orbitP5GapEquiv3
  | 4 => orbitP5GapEquiv4
  | 5 => orbitP5GapEquiv5

end Smallgroups.UsefulTheorems.Order32Certificate
