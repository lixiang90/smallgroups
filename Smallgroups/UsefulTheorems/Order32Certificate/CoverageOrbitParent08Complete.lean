/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Reduction
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08GapCore

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

theorem orbitP8_cocycle_gap_complete
    (f : Order16Table.Q parent8Table → Order16Table.Q parent8Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ j : Fin 51, Nonempty (CocycleGroup f hf ≃* smallGroup32 j) := by
  obtain ⟨o, ⟨e⟩⟩ := orbitP8_cocycle_orbit_complete f hf
  exact ⟨orbitP8GapIndex o, ⟨e.trans (orbitP8SelectedGapEquiv o)⟩⟩

end Smallgroups.UsefulTheorems.Order32Certificate
