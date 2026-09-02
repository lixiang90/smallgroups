/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04AlignmentPart04
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04AlignmentPart05
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04AlignmentPart06
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP4GapIndex : Fin 6 → Fin 51 :=
  ![22, 13, 12, 1, 11, 14]
noncomputable def orbitP4SelectedGapEquiv : ∀ o : Fin 6,
    CocycleGroup (orbitP4SelectedCocycle o) (orbitP4SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP4GapIndex o)
  | 0 => orbitP4GapEquiv0
  | 1 => orbitP4GapEquiv1
  | 2 => orbitP4GapEquiv2
  | 3 => orbitP4GapEquiv3
  | 4 => orbitP4GapEquiv4
  | 5 => orbitP4GapEquiv5

end Smallgroups.UsefulTheorems.Order32Certificate
