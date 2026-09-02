/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10PathPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10PathPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10PathPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10PathPart04

namespace Smallgroups.UsefulTheorems.Order32Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Enumerating every finite coefficient vector selects its checked normalization equivalence.
theorem orbitP10NormalizeEquiv_nonempty (k : Fin 64) : Nonempty (
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index k))
        (orbitP10SelectedCocycle_consistent (orbitP10Index k)) ≃*
      CocycleGroup (orbitP10TargetCocycle k) (orbitP10TargetCocycle_consistent k)) := by
  fin_cases k
  · exact ⟨orbitP10NormalizeEquiv0⟩
  · exact ⟨orbitP10NormalizeEquiv1⟩
  · exact ⟨orbitP10NormalizeEquiv2⟩
  · exact ⟨orbitP10NormalizeEquiv3⟩
  · exact ⟨orbitP10NormalizeEquiv4⟩
  · exact ⟨orbitP10NormalizeEquiv5⟩
  · exact ⟨orbitP10NormalizeEquiv6⟩
  · exact ⟨orbitP10NormalizeEquiv7⟩
  · exact ⟨orbitP10NormalizeEquiv8⟩
  · exact ⟨orbitP10NormalizeEquiv9⟩
  · exact ⟨orbitP10NormalizeEquiv10⟩
  · exact ⟨orbitP10NormalizeEquiv11⟩
  · exact ⟨orbitP10NormalizeEquiv12⟩
  · exact ⟨orbitP10NormalizeEquiv13⟩
  · exact ⟨orbitP10NormalizeEquiv14⟩
  · exact ⟨orbitP10NormalizeEquiv15⟩
  · exact ⟨orbitP10NormalizeEquiv16⟩
  · exact ⟨orbitP10NormalizeEquiv17⟩
  · exact ⟨orbitP10NormalizeEquiv18⟩
  · exact ⟨orbitP10NormalizeEquiv19⟩
  · exact ⟨orbitP10NormalizeEquiv20⟩
  · exact ⟨orbitP10NormalizeEquiv21⟩
  · exact ⟨orbitP10NormalizeEquiv22⟩
  · exact ⟨orbitP10NormalizeEquiv23⟩
  · exact ⟨orbitP10NormalizeEquiv24⟩
  · exact ⟨orbitP10NormalizeEquiv25⟩
  · exact ⟨orbitP10NormalizeEquiv26⟩
  · exact ⟨orbitP10NormalizeEquiv27⟩
  · exact ⟨orbitP10NormalizeEquiv28⟩
  · exact ⟨orbitP10NormalizeEquiv29⟩
  · exact ⟨orbitP10NormalizeEquiv30⟩
  · exact ⟨orbitP10NormalizeEquiv31⟩
  · exact ⟨orbitP10NormalizeEquiv32⟩
  · exact ⟨orbitP10NormalizeEquiv33⟩
  · exact ⟨orbitP10NormalizeEquiv34⟩
  · exact ⟨orbitP10NormalizeEquiv35⟩
  · exact ⟨orbitP10NormalizeEquiv36⟩
  · exact ⟨orbitP10NormalizeEquiv37⟩
  · exact ⟨orbitP10NormalizeEquiv38⟩
  · exact ⟨orbitP10NormalizeEquiv39⟩
  · exact ⟨orbitP10NormalizeEquiv40⟩
  · exact ⟨orbitP10NormalizeEquiv41⟩
  · exact ⟨orbitP10NormalizeEquiv42⟩
  · exact ⟨orbitP10NormalizeEquiv43⟩
  · exact ⟨orbitP10NormalizeEquiv44⟩
  · exact ⟨orbitP10NormalizeEquiv45⟩
  · exact ⟨orbitP10NormalizeEquiv46⟩
  · exact ⟨orbitP10NormalizeEquiv47⟩
  · exact ⟨orbitP10NormalizeEquiv48⟩
  · exact ⟨orbitP10NormalizeEquiv49⟩
  · exact ⟨orbitP10NormalizeEquiv50⟩
  · exact ⟨orbitP10NormalizeEquiv51⟩
  · exact ⟨orbitP10NormalizeEquiv52⟩
  · exact ⟨orbitP10NormalizeEquiv53⟩
  · exact ⟨orbitP10NormalizeEquiv54⟩
  · exact ⟨orbitP10NormalizeEquiv55⟩
  · exact ⟨orbitP10NormalizeEquiv56⟩
  · exact ⟨orbitP10NormalizeEquiv57⟩
  · exact ⟨orbitP10NormalizeEquiv58⟩
  · exact ⟨orbitP10NormalizeEquiv59⟩
  · exact ⟨orbitP10NormalizeEquiv60⟩
  · exact ⟨orbitP10NormalizeEquiv61⟩
  · exact ⟨orbitP10NormalizeEquiv62⟩
  · exact ⟨orbitP10NormalizeEquiv63⟩

noncomputable def orbitP10NormalizeEquiv (k : Fin 64) :
    CocycleGroup (orbitP10SelectedCocycle (orbitP10Index k))
        (orbitP10SelectedCocycle_consistent (orbitP10Index k)) ≃*
      CocycleGroup (orbitP10TargetCocycle k) (orbitP10TargetCocycle_consistent k) :=
  (orbitP10NormalizeEquiv_nonempty k).some

end Smallgroups.UsefulTheorems.Order32Certificate
