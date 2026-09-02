/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03Reduction
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03GapCore

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

theorem orbitP3_cocycle_gap_complete
    (f : Order16Table.Q parent3Table → Order16Table.Q parent3Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ j : Fin 51, Nonempty (CocycleGroup f hf ≃* smallGroup32 j) := by
  obtain ⟨o, ⟨e⟩⟩ := orbitP3_cocycle_orbit_complete f hf
  exact ⟨orbitP3GapIndex o, ⟨e.trans (orbitP3SelectedGapEquiv o)⟩⟩

end Smallgroups.UsefulTheorems.Order32Certificate
