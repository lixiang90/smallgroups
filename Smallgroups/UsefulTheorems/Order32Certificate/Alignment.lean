/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart01
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart02
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart03
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart04
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart05
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart06
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart07
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart08
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart09
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart10
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart11
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart12
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart13
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart14
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart15
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart16
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart17
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart18
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart19
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart20
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart21
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart22
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart23
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart24
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart25
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart26
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart27
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart28
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart29
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart30
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart31
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart32
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart33
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart34
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart35
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart36
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart37
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart38
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart39
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart40
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart41
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart42
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart43
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart44
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart45
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart46
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart47
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart48
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart49
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart50
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart51
import Smallgroups.UsefulTheorems.Order32Certificate.Family
import Smallgroups.GAP.Order32

/-! Generated GAP alignment for all 51 representatives. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

noncomputable def generatedFamilyGapEquivPart01 : ∀ i : Fin 8,
    generatedFamilyPart01 i ≃* PCGroup (smallPres32Part01 i)
  | 0 => generatedGapEquiv1
  | 1 => generatedGapEquiv2
  | 2 => generatedGapEquiv3
  | 3 => generatedGapEquiv4
  | 4 => generatedGapEquiv5
  | 5 => generatedGapEquiv6
  | 6 => generatedGapEquiv7
  | 7 => generatedGapEquiv8

noncomputable def generatedFamilyGapEquivPart02 : ∀ i : Fin 8,
    generatedFamilyPart02 i ≃* PCGroup (smallPres32Part02 i)
  | 0 => generatedGapEquiv9
  | 1 => generatedGapEquiv10
  | 2 => generatedGapEquiv11
  | 3 => generatedGapEquiv12
  | 4 => generatedGapEquiv13
  | 5 => generatedGapEquiv14
  | 6 => generatedGapEquiv15
  | 7 => generatedGapEquiv16

noncomputable def generatedFamilyGapEquivPart03 : ∀ i : Fin 8,
    generatedFamilyPart03 i ≃* PCGroup (smallPres32Part03 i)
  | 0 => generatedGapEquiv17
  | 1 => generatedGapEquiv18
  | 2 => generatedGapEquiv19
  | 3 => generatedGapEquiv20
  | 4 => generatedGapEquiv21
  | 5 => generatedGapEquiv22
  | 6 => generatedGapEquiv23
  | 7 => generatedGapEquiv24

noncomputable def generatedFamilyGapEquivPart04 : ∀ i : Fin 8,
    generatedFamilyPart04 i ≃* PCGroup (smallPres32Part04 i)
  | 0 => generatedGapEquiv25
  | 1 => generatedGapEquiv26
  | 2 => generatedGapEquiv27
  | 3 => generatedGapEquiv28
  | 4 => generatedGapEquiv29
  | 5 => generatedGapEquiv30
  | 6 => generatedGapEquiv31
  | 7 => generatedGapEquiv32

noncomputable def generatedFamilyGapEquivPart05 : ∀ i : Fin 8,
    generatedFamilyPart05 i ≃* PCGroup (smallPres32Part05 i)
  | 0 => generatedGapEquiv33
  | 1 => generatedGapEquiv34
  | 2 => generatedGapEquiv35
  | 3 => generatedGapEquiv36
  | 4 => generatedGapEquiv37
  | 5 => generatedGapEquiv38
  | 6 => generatedGapEquiv39
  | 7 => generatedGapEquiv40

noncomputable def generatedFamilyGapEquivPart06 : ∀ i : Fin 8,
    generatedFamilyPart06 i ≃* PCGroup (smallPres32Part06 i)
  | 0 => generatedGapEquiv41
  | 1 => generatedGapEquiv42
  | 2 => generatedGapEquiv43
  | 3 => generatedGapEquiv44
  | 4 => generatedGapEquiv45
  | 5 => generatedGapEquiv46
  | 6 => generatedGapEquiv47
  | 7 => generatedGapEquiv48

noncomputable def generatedFamilyGapEquivPart07 : ∀ i : Fin 3,
    generatedFamilyPart07 i ≃* PCGroup (smallPres32Part07 i)
  | 0 => generatedGapEquiv49
  | 1 => generatedGapEquiv50
  | 2 => generatedGapEquiv51

theorem generatedFamilyGapEquiv_nonempty (i : Fin 51) :
    Nonempty (generatedFamily i ≃* smallGroup32 i) := by
  fin_cases i
  · exact ⟨generatedGapEquiv1⟩
  · exact ⟨generatedGapEquiv2⟩
  · exact ⟨generatedGapEquiv3⟩
  · exact ⟨generatedGapEquiv4⟩
  · exact ⟨generatedGapEquiv5⟩
  · exact ⟨generatedGapEquiv6⟩
  · exact ⟨generatedGapEquiv7⟩
  · exact ⟨generatedGapEquiv8⟩
  · exact ⟨generatedGapEquiv9⟩
  · exact ⟨generatedGapEquiv10⟩
  · exact ⟨generatedGapEquiv11⟩
  · exact ⟨generatedGapEquiv12⟩
  · exact ⟨generatedGapEquiv13⟩
  · exact ⟨generatedGapEquiv14⟩
  · exact ⟨generatedGapEquiv15⟩
  · exact ⟨generatedGapEquiv16⟩
  · exact ⟨generatedGapEquiv17⟩
  · exact ⟨generatedGapEquiv18⟩
  · exact ⟨generatedGapEquiv19⟩
  · exact ⟨generatedGapEquiv20⟩
  · exact ⟨generatedGapEquiv21⟩
  · exact ⟨generatedGapEquiv22⟩
  · exact ⟨generatedGapEquiv23⟩
  · exact ⟨generatedGapEquiv24⟩
  · exact ⟨generatedGapEquiv25⟩
  · exact ⟨generatedGapEquiv26⟩
  · exact ⟨generatedGapEquiv27⟩
  · exact ⟨generatedGapEquiv28⟩
  · exact ⟨generatedGapEquiv29⟩
  · exact ⟨generatedGapEquiv30⟩
  · exact ⟨generatedGapEquiv31⟩
  · exact ⟨generatedGapEquiv32⟩
  · exact ⟨generatedGapEquiv33⟩
  · exact ⟨generatedGapEquiv34⟩
  · exact ⟨generatedGapEquiv35⟩
  · exact ⟨generatedGapEquiv36⟩
  · exact ⟨generatedGapEquiv37⟩
  · exact ⟨generatedGapEquiv38⟩
  · exact ⟨generatedGapEquiv39⟩
  · exact ⟨generatedGapEquiv40⟩
  · exact ⟨generatedGapEquiv41⟩
  · exact ⟨generatedGapEquiv42⟩
  · exact ⟨generatedGapEquiv43⟩
  · exact ⟨generatedGapEquiv44⟩
  · exact ⟨generatedGapEquiv45⟩
  · exact ⟨generatedGapEquiv46⟩
  · exact ⟨generatedGapEquiv47⟩
  · exact ⟨generatedGapEquiv48⟩
  · exact ⟨generatedGapEquiv49⟩
  · exact ⟨generatedGapEquiv50⟩
  · exact ⟨generatedGapEquiv51⟩

noncomputable def generatedFamilyGapEquiv (i : Fin 51) :
    generatedFamily i ≃* smallGroup32 i :=
  (generatedFamilyGapEquiv_nonempty i).some

end Smallgroups.UsefulTheorems.Order32Certificate
