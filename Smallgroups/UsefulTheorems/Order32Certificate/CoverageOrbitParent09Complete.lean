/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Reduction
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09GapCore

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

theorem orbitP9_cocycle_gap_complete
    (f : Order16Table.Q parent9Table → Order16Table.Q parent9Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ j : Fin 51, Nonempty (CocycleGroup f hf ≃* smallGroup32 j) := by
  obtain ⟨o, ⟨e⟩⟩ := orbitP9_cocycle_orbit_complete f hf
  exact ⟨orbitP9GapIndex o, ⟨e.trans (orbitP9SelectedGapEquiv o)⟩⟩

end Smallgroups.UsefulTheorems.Order32Certificate
