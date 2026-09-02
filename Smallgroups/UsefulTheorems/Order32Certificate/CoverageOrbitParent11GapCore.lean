/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart04
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart05
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart06
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart07
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart08
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart09
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart10
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart11
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart12
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart13
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart14
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart15
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart16
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart17
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11AlignmentPart18
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def orbitP11GapIndex : Fin 18 → Fin 51 :=
  ![45, 24, 33, 27, 27, 26, 22, 34, 29, 28, 30, 21, 42, 38, 41, 43, 40, 39]
theorem orbitP11SelectedGapEquiv_nonempty (o : Fin 18) : Nonempty (
    CocycleGroup (orbitP11SelectedCocycle o) (orbitP11SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP11GapIndex o)) := by
  fin_cases o
  · exact ⟨orbitP11GapEquiv0⟩
  · exact ⟨orbitP11GapEquiv1⟩
  · exact ⟨orbitP11GapEquiv2⟩
  · exact ⟨orbitP11GapEquiv3⟩
  · exact ⟨orbitP11GapEquiv4⟩
  · exact ⟨orbitP11GapEquiv5⟩
  · exact ⟨orbitP11GapEquiv6⟩
  · exact ⟨orbitP11GapEquiv7⟩
  · exact ⟨orbitP11GapEquiv8⟩
  · exact ⟨orbitP11GapEquiv9⟩
  · exact ⟨orbitP11GapEquiv10⟩
  · exact ⟨orbitP11GapEquiv11⟩
  · exact ⟨orbitP11GapEquiv12⟩
  · exact ⟨orbitP11GapEquiv13⟩
  · exact ⟨orbitP11GapEquiv14⟩
  · exact ⟨orbitP11GapEquiv15⟩
  · exact ⟨orbitP11GapEquiv16⟩
  · exact ⟨orbitP11GapEquiv17⟩

noncomputable def orbitP11SelectedGapEquiv (o : Fin 18) :
    CocycleGroup (orbitP11SelectedCocycle o) (orbitP11SelectedCocycle_consistent o) ≃*
      smallGroup32 (orbitP11GapIndex o) :=
  (orbitP11SelectedGapEquiv_nonempty o).some

end Smallgroups.UsefulTheorems.Order32Certificate
