/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05PathPart01

namespace Smallgroups.UsefulTheorems.Order32Certificate

noncomputable def orbitP5NormalizeEquiv : ∀ k : Fin 8,
    CocycleGroup (orbitP5SelectedCocycle (orbitP5Index k))
        (orbitP5SelectedCocycle_consistent (orbitP5Index k)) ≃*
      CocycleGroup (orbitP5TargetCocycle k) (orbitP5TargetCocycle_consistent k)
  | 0 => orbitP5NormalizeEquiv0
  | 1 => orbitP5NormalizeEquiv1
  | 2 => orbitP5NormalizeEquiv2
  | 3 => orbitP5NormalizeEquiv3
  | 4 => orbitP5NormalizeEquiv4
  | 5 => orbitP5NormalizeEquiv5
  | 6 => orbitP5NormalizeEquiv6
  | 7 => orbitP5NormalizeEquiv7

end Smallgroups.UsefulTheorems.Order32Certificate
