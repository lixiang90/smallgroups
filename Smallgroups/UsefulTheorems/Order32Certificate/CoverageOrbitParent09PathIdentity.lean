/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09PathPart01

namespace Smallgroups.UsefulTheorems.Order32Certificate

noncomputable def orbitP9NormalizeEquiv : ∀ k : Fin 4,
    CocycleGroup (orbitP9SelectedCocycle (orbitP9Index k))
        (orbitP9SelectedCocycle_consistent (orbitP9Index k)) ≃*
      CocycleGroup (orbitP9TargetCocycle k) (orbitP9TargetCocycle_consistent k)
  | 0 => orbitP9NormalizeEquiv0
  | 1 => orbitP9NormalizeEquiv1
  | 2 => orbitP9NormalizeEquiv2
  | 3 => orbitP9NormalizeEquiv3

end Smallgroups.UsefulTheorems.Order32Certificate
