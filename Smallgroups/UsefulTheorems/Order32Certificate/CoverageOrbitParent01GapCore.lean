/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01AlignmentPart02
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP1GapIndex : Fin 2 → Fin 51 :=
  ![15, 0]
noncomputable def orbitP1SelectedGapEquiv : ∀ o : Fin 2,
    CocycleGroup (orbitP1SelectedCocycle o) (orbitP1SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP1GapIndex o)
  | 0 => orbitP1GapEquiv0
  | 1 => orbitP1GapEquiv1

end Smallgroups.UsefulTheorems.Order32Certificate
