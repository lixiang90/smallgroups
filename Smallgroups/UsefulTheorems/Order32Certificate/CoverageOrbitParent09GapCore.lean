/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09AlignmentPart03
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP9GapIndex : Fin 3 → Fin 51 :=
  ![40, 13, 9]
noncomputable def orbitP9SelectedGapEquiv : ∀ o : Fin 3,
    CocycleGroup (orbitP9SelectedCocycle o) (orbitP9SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP9GapIndex o)
  | 0 => orbitP9GapEquiv0
  | 1 => orbitP9GapEquiv1
  | 2 => orbitP9GapEquiv2

end Smallgroups.UsefulTheorems.Order32Certificate
