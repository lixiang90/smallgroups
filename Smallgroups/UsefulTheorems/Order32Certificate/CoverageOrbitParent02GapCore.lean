/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02AlignmentPart04
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP2GapIndex : Fin 4 → Fin 51 :=
  ![20, 2, 1, 3]
noncomputable def orbitP2SelectedGapEquiv : ∀ o : Fin 4,
    CocycleGroup (orbitP2SelectedCocycle o) (orbitP2SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP2GapIndex o)
  | 0 => orbitP2GapEquiv0
  | 1 => orbitP2GapEquiv1
  | 2 => orbitP2GapEquiv2
  | 3 => orbitP2GapEquiv3

end Smallgroups.UsefulTheorems.Order32Certificate
