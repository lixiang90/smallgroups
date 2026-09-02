/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Reduction
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12GapCore

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

theorem orbitP12_cocycle_gap_complete
    (f : Order16Table.Q parent12Table → Order16Table.Q parent12Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ j : Fin 51, Nonempty (CocycleGroup f hf ≃* smallGroup32 j) := by
  obtain ⟨o, ⟨e⟩⟩ := orbitP12_cocycle_orbit_complete f hf
  exact ⟨orbitP12GapIndex o, ⟨e.trans (orbitP12SelectedGapEquiv o)⟩⟩

end Smallgroups.UsefulTheorems.Order32Certificate
