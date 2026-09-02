/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08PathPart01

namespace Smallgroups.UsefulTheorems.Order32Certificate

noncomputable def orbitP8NormalizeEquiv : ∀ k : Fin 4,
    CocycleGroup (orbitP8SelectedCocycle (orbitP8Index k))
        (orbitP8SelectedCocycle_consistent (orbitP8Index k)) ≃*
      CocycleGroup (orbitP8TargetCocycle k) (orbitP8TargetCocycle_consistent k)
  | 0 => orbitP8NormalizeEquiv0
  | 1 => orbitP8NormalizeEquiv1
  | 2 => orbitP8NormalizeEquiv2
  | 3 => orbitP8NormalizeEquiv3

end Smallgroups.UsefulTheorems.Order32Certificate
