/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11PathPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11PathPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11PathPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11PathPart04

namespace Smallgroups.UsefulTheorems.Order32Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Enumerating every finite coefficient vector selects its checked normalization equivalence.
theorem orbitP11NormalizeEquiv_nonempty (k : Fin 64) : Nonempty (
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index k))
        (orbitP11SelectedCocycle_consistent (orbitP11Index k)) ≃*
      CocycleGroup (orbitP11TargetCocycle k) (orbitP11TargetCocycle_consistent k)) := by
  fin_cases k
  · exact ⟨orbitP11NormalizeEquiv0⟩
  · exact ⟨orbitP11NormalizeEquiv1⟩
  · exact ⟨orbitP11NormalizeEquiv2⟩
  · exact ⟨orbitP11NormalizeEquiv3⟩
  · exact ⟨orbitP11NormalizeEquiv4⟩
  · exact ⟨orbitP11NormalizeEquiv5⟩
  · exact ⟨orbitP11NormalizeEquiv6⟩
  · exact ⟨orbitP11NormalizeEquiv7⟩
  · exact ⟨orbitP11NormalizeEquiv8⟩
  · exact ⟨orbitP11NormalizeEquiv9⟩
  · exact ⟨orbitP11NormalizeEquiv10⟩
  · exact ⟨orbitP11NormalizeEquiv11⟩
  · exact ⟨orbitP11NormalizeEquiv12⟩
  · exact ⟨orbitP11NormalizeEquiv13⟩
  · exact ⟨orbitP11NormalizeEquiv14⟩
  · exact ⟨orbitP11NormalizeEquiv15⟩
  · exact ⟨orbitP11NormalizeEquiv16⟩
  · exact ⟨orbitP11NormalizeEquiv17⟩
  · exact ⟨orbitP11NormalizeEquiv18⟩
  · exact ⟨orbitP11NormalizeEquiv19⟩
  · exact ⟨orbitP11NormalizeEquiv20⟩
  · exact ⟨orbitP11NormalizeEquiv21⟩
  · exact ⟨orbitP11NormalizeEquiv22⟩
  · exact ⟨orbitP11NormalizeEquiv23⟩
  · exact ⟨orbitP11NormalizeEquiv24⟩
  · exact ⟨orbitP11NormalizeEquiv25⟩
  · exact ⟨orbitP11NormalizeEquiv26⟩
  · exact ⟨orbitP11NormalizeEquiv27⟩
  · exact ⟨orbitP11NormalizeEquiv28⟩
  · exact ⟨orbitP11NormalizeEquiv29⟩
  · exact ⟨orbitP11NormalizeEquiv30⟩
  · exact ⟨orbitP11NormalizeEquiv31⟩
  · exact ⟨orbitP11NormalizeEquiv32⟩
  · exact ⟨orbitP11NormalizeEquiv33⟩
  · exact ⟨orbitP11NormalizeEquiv34⟩
  · exact ⟨orbitP11NormalizeEquiv35⟩
  · exact ⟨orbitP11NormalizeEquiv36⟩
  · exact ⟨orbitP11NormalizeEquiv37⟩
  · exact ⟨orbitP11NormalizeEquiv38⟩
  · exact ⟨orbitP11NormalizeEquiv39⟩
  · exact ⟨orbitP11NormalizeEquiv40⟩
  · exact ⟨orbitP11NormalizeEquiv41⟩
  · exact ⟨orbitP11NormalizeEquiv42⟩
  · exact ⟨orbitP11NormalizeEquiv43⟩
  · exact ⟨orbitP11NormalizeEquiv44⟩
  · exact ⟨orbitP11NormalizeEquiv45⟩
  · exact ⟨orbitP11NormalizeEquiv46⟩
  · exact ⟨orbitP11NormalizeEquiv47⟩
  · exact ⟨orbitP11NormalizeEquiv48⟩
  · exact ⟨orbitP11NormalizeEquiv49⟩
  · exact ⟨orbitP11NormalizeEquiv50⟩
  · exact ⟨orbitP11NormalizeEquiv51⟩
  · exact ⟨orbitP11NormalizeEquiv52⟩
  · exact ⟨orbitP11NormalizeEquiv53⟩
  · exact ⟨orbitP11NormalizeEquiv54⟩
  · exact ⟨orbitP11NormalizeEquiv55⟩
  · exact ⟨orbitP11NormalizeEquiv56⟩
  · exact ⟨orbitP11NormalizeEquiv57⟩
  · exact ⟨orbitP11NormalizeEquiv58⟩
  · exact ⟨orbitP11NormalizeEquiv59⟩
  · exact ⟨orbitP11NormalizeEquiv60⟩
  · exact ⟨orbitP11NormalizeEquiv61⟩
  · exact ⟨orbitP11NormalizeEquiv62⟩
  · exact ⟨orbitP11NormalizeEquiv63⟩

noncomputable def orbitP11NormalizeEquiv (k : Fin 64) :
    CocycleGroup (orbitP11SelectedCocycle (orbitP11Index k))
        (orbitP11SelectedCocycle_consistent (orbitP11Index k)) ≃*
      CocycleGroup (orbitP11TargetCocycle k) (orbitP11TargetCocycle_consistent k) :=
  (orbitP11NormalizeEquiv_nonempty k).some

end Smallgroups.UsefulTheorems.Order32Certificate
