/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01PathPart01

namespace Smallgroups.UsefulTheorems.Order32Certificate

noncomputable def orbitP1NormalizeEquiv : ∀ k : Fin 2,
    CocycleGroup (orbitP1SelectedCocycle (orbitP1Index k))
        (orbitP1SelectedCocycle_consistent (orbitP1Index k)) ≃*
      CocycleGroup (orbitP1TargetCocycle k) (orbitP1TargetCocycle_consistent k)
  | 0 => orbitP1NormalizeEquiv0
  | 1 => orbitP1NormalizeEquiv1

end Smallgroups.UsefulTheorems.Order32Certificate
