/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13PathPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13PathPart02

namespace Smallgroups.UsefulTheorems.Order32Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Enumerating every finite coefficient vector selects its checked normalization equivalence.
theorem orbitP13NormalizeEquiv_nonempty (k : Fin 32) : Nonempty (
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index k))
        (orbitP13SelectedCocycle_consistent (orbitP13Index k)) ≃*
      CocycleGroup (orbitP13TargetCocycle k) (orbitP13TargetCocycle_consistent k)) := by
  fin_cases k
  · exact ⟨orbitP13NormalizeEquiv0⟩
  · exact ⟨orbitP13NormalizeEquiv1⟩
  · exact ⟨orbitP13NormalizeEquiv2⟩
  · exact ⟨orbitP13NormalizeEquiv3⟩
  · exact ⟨orbitP13NormalizeEquiv4⟩
  · exact ⟨orbitP13NormalizeEquiv5⟩
  · exact ⟨orbitP13NormalizeEquiv6⟩
  · exact ⟨orbitP13NormalizeEquiv7⟩
  · exact ⟨orbitP13NormalizeEquiv8⟩
  · exact ⟨orbitP13NormalizeEquiv9⟩
  · exact ⟨orbitP13NormalizeEquiv10⟩
  · exact ⟨orbitP13NormalizeEquiv11⟩
  · exact ⟨orbitP13NormalizeEquiv12⟩
  · exact ⟨orbitP13NormalizeEquiv13⟩
  · exact ⟨orbitP13NormalizeEquiv14⟩
  · exact ⟨orbitP13NormalizeEquiv15⟩
  · exact ⟨orbitP13NormalizeEquiv16⟩
  · exact ⟨orbitP13NormalizeEquiv17⟩
  · exact ⟨orbitP13NormalizeEquiv18⟩
  · exact ⟨orbitP13NormalizeEquiv19⟩
  · exact ⟨orbitP13NormalizeEquiv20⟩
  · exact ⟨orbitP13NormalizeEquiv21⟩
  · exact ⟨orbitP13NormalizeEquiv22⟩
  · exact ⟨orbitP13NormalizeEquiv23⟩
  · exact ⟨orbitP13NormalizeEquiv24⟩
  · exact ⟨orbitP13NormalizeEquiv25⟩
  · exact ⟨orbitP13NormalizeEquiv26⟩
  · exact ⟨orbitP13NormalizeEquiv27⟩
  · exact ⟨orbitP13NormalizeEquiv28⟩
  · exact ⟨orbitP13NormalizeEquiv29⟩
  · exact ⟨orbitP13NormalizeEquiv30⟩
  · exact ⟨orbitP13NormalizeEquiv31⟩

noncomputable def orbitP13NormalizeEquiv (k : Fin 32) :
    CocycleGroup (orbitP13SelectedCocycle (orbitP13Index k))
        (orbitP13SelectedCocycle_consistent (orbitP13Index k)) ≃*
      CocycleGroup (orbitP13TargetCocycle k) (orbitP13TargetCocycle_consistent k) :=
  (orbitP13NormalizeEquiv_nonempty k).some

end Smallgroups.UsefulTheorems.Order32Certificate
