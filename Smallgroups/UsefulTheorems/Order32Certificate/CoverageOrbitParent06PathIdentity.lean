/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06PathPart01

namespace Smallgroups.UsefulTheorems.Order32Certificate

noncomputable def orbitP6NormalizeEquiv : ∀ k : Fin 4,
    CocycleGroup (orbitP6SelectedCocycle (orbitP6Index k))
        (orbitP6SelectedCocycle_consistent (orbitP6Index k)) ≃*
      CocycleGroup (orbitP6TargetCocycle k) (orbitP6TargetCocycle_consistent k)
  | 0 => orbitP6NormalizeEquiv0
  | 1 => orbitP6NormalizeEquiv1
  | 2 => orbitP6NormalizeEquiv2
  | 3 => orbitP6NormalizeEquiv3

end Smallgroups.UsefulTheorems.Order32Certificate
