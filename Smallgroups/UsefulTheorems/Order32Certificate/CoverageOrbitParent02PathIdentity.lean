/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02PathPart01

namespace Smallgroups.UsefulTheorems.Order32Certificate

noncomputable def orbitP2NormalizeEquiv : ∀ k : Fin 8,
    CocycleGroup (orbitP2SelectedCocycle (orbitP2Index k))
        (orbitP2SelectedCocycle_consistent (orbitP2Index k)) ≃*
      CocycleGroup (orbitP2TargetCocycle k) (orbitP2TargetCocycle_consistent k)
  | 0 => orbitP2NormalizeEquiv0
  | 1 => orbitP2NormalizeEquiv1
  | 2 => orbitP2NormalizeEquiv2
  | 3 => orbitP2NormalizeEquiv3
  | 4 => orbitP2NormalizeEquiv4
  | 5 => orbitP2NormalizeEquiv5
  | 6 => orbitP2NormalizeEquiv6
  | 7 => orbitP2NormalizeEquiv7

end Smallgroups.UsefulTheorems.Order32Certificate
