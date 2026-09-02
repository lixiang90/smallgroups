/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04PathPart01

namespace Smallgroups.UsefulTheorems.Order32Certificate

noncomputable def orbitP4NormalizeEquiv : ∀ k : Fin 8,
    CocycleGroup (orbitP4SelectedCocycle (orbitP4Index k))
        (orbitP4SelectedCocycle_consistent (orbitP4Index k)) ≃*
      CocycleGroup (orbitP4TargetCocycle k) (orbitP4TargetCocycle_consistent k)
  | 0 => orbitP4NormalizeEquiv0
  | 1 => orbitP4NormalizeEquiv1
  | 2 => orbitP4NormalizeEquiv2
  | 3 => orbitP4NormalizeEquiv3
  | 4 => orbitP4NormalizeEquiv4
  | 5 => orbitP4NormalizeEquiv5
  | 6 => orbitP4NormalizeEquiv6
  | 7 => orbitP4NormalizeEquiv7

end Smallgroups.UsefulTheorems.Order32Certificate
