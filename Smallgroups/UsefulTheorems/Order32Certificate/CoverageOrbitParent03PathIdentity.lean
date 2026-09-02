/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03PathPart01

namespace Smallgroups.UsefulTheorems.Order32Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Enumerating every finite coefficient vector selects its checked normalization equivalence.
theorem orbitP3NormalizeEquiv_nonempty (k : Fin 16) : Nonempty (
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index k))
        (orbitP3SelectedCocycle_consistent (orbitP3Index k)) ≃*
      CocycleGroup (orbitP3TargetCocycle k) (orbitP3TargetCocycle_consistent k)) := by
  fin_cases k
  · exact ⟨orbitP3NormalizeEquiv0⟩
  · exact ⟨orbitP3NormalizeEquiv1⟩
  · exact ⟨orbitP3NormalizeEquiv2⟩
  · exact ⟨orbitP3NormalizeEquiv3⟩
  · exact ⟨orbitP3NormalizeEquiv4⟩
  · exact ⟨orbitP3NormalizeEquiv5⟩
  · exact ⟨orbitP3NormalizeEquiv6⟩
  · exact ⟨orbitP3NormalizeEquiv7⟩
  · exact ⟨orbitP3NormalizeEquiv8⟩
  · exact ⟨orbitP3NormalizeEquiv9⟩
  · exact ⟨orbitP3NormalizeEquiv10⟩
  · exact ⟨orbitP3NormalizeEquiv11⟩
  · exact ⟨orbitP3NormalizeEquiv12⟩
  · exact ⟨orbitP3NormalizeEquiv13⟩
  · exact ⟨orbitP3NormalizeEquiv14⟩
  · exact ⟨orbitP3NormalizeEquiv15⟩

noncomputable def orbitP3NormalizeEquiv (k : Fin 16) :
    CocycleGroup (orbitP3SelectedCocycle (orbitP3Index k))
        (orbitP3SelectedCocycle_consistent (orbitP3Index k)) ≃*
      CocycleGroup (orbitP3TargetCocycle k) (orbitP3TargetCocycle_consistent k) :=
  (orbitP3NormalizeEquiv_nonempty k).some

end Smallgroups.UsefulTheorems.Order32Certificate
