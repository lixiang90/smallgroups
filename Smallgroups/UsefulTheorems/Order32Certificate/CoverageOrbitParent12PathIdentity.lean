/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12PathPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12PathPart02

namespace Smallgroups.UsefulTheorems.Order32Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Enumerating every finite coefficient vector selects its checked normalization equivalence.
theorem orbitP12NormalizeEquiv_nonempty (k : Fin 32) : Nonempty (
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index k))
        (orbitP12SelectedCocycle_consistent (orbitP12Index k)) ≃*
      CocycleGroup (orbitP12TargetCocycle k) (orbitP12TargetCocycle_consistent k)) := by
  fin_cases k
  · exact ⟨orbitP12NormalizeEquiv0⟩
  · exact ⟨orbitP12NormalizeEquiv1⟩
  · exact ⟨orbitP12NormalizeEquiv2⟩
  · exact ⟨orbitP12NormalizeEquiv3⟩
  · exact ⟨orbitP12NormalizeEquiv4⟩
  · exact ⟨orbitP12NormalizeEquiv5⟩
  · exact ⟨orbitP12NormalizeEquiv6⟩
  · exact ⟨orbitP12NormalizeEquiv7⟩
  · exact ⟨orbitP12NormalizeEquiv8⟩
  · exact ⟨orbitP12NormalizeEquiv9⟩
  · exact ⟨orbitP12NormalizeEquiv10⟩
  · exact ⟨orbitP12NormalizeEquiv11⟩
  · exact ⟨orbitP12NormalizeEquiv12⟩
  · exact ⟨orbitP12NormalizeEquiv13⟩
  · exact ⟨orbitP12NormalizeEquiv14⟩
  · exact ⟨orbitP12NormalizeEquiv15⟩
  · exact ⟨orbitP12NormalizeEquiv16⟩
  · exact ⟨orbitP12NormalizeEquiv17⟩
  · exact ⟨orbitP12NormalizeEquiv18⟩
  · exact ⟨orbitP12NormalizeEquiv19⟩
  · exact ⟨orbitP12NormalizeEquiv20⟩
  · exact ⟨orbitP12NormalizeEquiv21⟩
  · exact ⟨orbitP12NormalizeEquiv22⟩
  · exact ⟨orbitP12NormalizeEquiv23⟩
  · exact ⟨orbitP12NormalizeEquiv24⟩
  · exact ⟨orbitP12NormalizeEquiv25⟩
  · exact ⟨orbitP12NormalizeEquiv26⟩
  · exact ⟨orbitP12NormalizeEquiv27⟩
  · exact ⟨orbitP12NormalizeEquiv28⟩
  · exact ⟨orbitP12NormalizeEquiv29⟩
  · exact ⟨orbitP12NormalizeEquiv30⟩
  · exact ⟨orbitP12NormalizeEquiv31⟩

noncomputable def orbitP12NormalizeEquiv (k : Fin 32) :
    CocycleGroup (orbitP12SelectedCocycle (orbitP12Index k))
        (orbitP12SelectedCocycle_consistent (orbitP12Index k)) ≃*
      CocycleGroup (orbitP12TargetCocycle k) (orbitP12TargetCocycle_consistent k) :=
  (orbitP12NormalizeEquiv_nonempty k).some

end Smallgroups.UsefulTheorems.Order32Certificate
