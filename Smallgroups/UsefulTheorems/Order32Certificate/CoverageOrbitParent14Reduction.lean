/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Parent14QuadraticClassification

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

/-- Coverage now follows from the structural seven-form theorem. -/
theorem orbitP14_cocycle_orbit_complete
    (f : Order16Table.Q parent14Table → Order16Table.Q parent14Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 7, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP14SelectedCocycle o) (orbitP14SelectedCocycle_consistent o)) :=
  parent14_extension_reduces_to_seven_structural f hf

end Smallgroups.UsefulTheorems.Order32Certificate
