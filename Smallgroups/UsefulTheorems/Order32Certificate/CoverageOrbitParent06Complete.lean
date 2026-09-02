/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Reduction
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06GapCore

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

theorem orbitP6_cocycle_gap_complete
    (f : Order16Table.Q parent6Table → Order16Table.Q parent6Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ j : Fin 51, Nonempty (CocycleGroup f hf ≃* smallGroup32 j) := by
  obtain ⟨o, ⟨e⟩⟩ := orbitP6_cocycle_orbit_complete f hf
  exact ⟨orbitP6GapIndex o, ⟨e.trans (orbitP6SelectedGapEquiv o)⟩⟩

end Smallgroups.UsefulTheorems.Order32Certificate
