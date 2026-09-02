/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07PathPart01

namespace Smallgroups.UsefulTheorems.Order32Certificate

noncomputable def orbitP7NormalizeEquiv : ∀ k : Fin 8,
    CocycleGroup (orbitP7SelectedCocycle (orbitP7Index k))
        (orbitP7SelectedCocycle_consistent (orbitP7Index k)) ≃*
      CocycleGroup (orbitP7TargetCocycle k) (orbitP7TargetCocycle_consistent k)
  | 0 => orbitP7NormalizeEquiv0
  | 1 => orbitP7NormalizeEquiv1
  | 2 => orbitP7NormalizeEquiv2
  | 3 => orbitP7NormalizeEquiv3
  | 4 => orbitP7NormalizeEquiv4
  | 5 => orbitP7NormalizeEquiv5
  | 6 => orbitP7NormalizeEquiv6
  | 7 => orbitP7NormalizeEquiv7

end Smallgroups.UsefulTheorems.Order32Certificate
