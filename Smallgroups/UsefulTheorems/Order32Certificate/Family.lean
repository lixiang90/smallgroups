/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Reps
import Mathlib.Tactic

/-! Generated fallback-free `Fin 51` family; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

abbrev generatedFamilyPart01 : Fin 8 → Type
  | 0 => generatedGroup1
  | 1 => generatedGroup2
  | 2 => generatedGroup3
  | 3 => generatedGroup4
  | 4 => generatedGroup5
  | 5 => generatedGroup6
  | 6 => generatedGroup7
  | 7 => generatedGroup8

instance instGroupGeneratedFamilyPart01 :
    ∀ i, Group (generatedFamilyPart01 i)
  | 0 => inferInstanceAs (Group generatedGroup1)
  | 1 => inferInstanceAs (Group generatedGroup2)
  | 2 => inferInstanceAs (Group generatedGroup3)
  | 3 => inferInstanceAs (Group generatedGroup4)
  | 4 => inferInstanceAs (Group generatedGroup5)
  | 5 => inferInstanceAs (Group generatedGroup6)
  | 6 => inferInstanceAs (Group generatedGroup7)
  | 7 => inferInstanceAs (Group generatedGroup8)

theorem card_generatedFamilyPart01 :
    ∀ i, Nat.card (generatedFamilyPart01 i) = 32
  | 0 => card_generatedGroup1
  | 1 => card_generatedGroup2
  | 2 => card_generatedGroup3
  | 3 => card_generatedGroup4
  | 4 => card_generatedGroup5
  | 5 => card_generatedGroup6
  | 6 => card_generatedGroup7
  | 7 => card_generatedGroup8

abbrev generatedFamilyPart02 : Fin 8 → Type
  | 0 => generatedGroup9
  | 1 => generatedGroup10
  | 2 => generatedGroup11
  | 3 => generatedGroup12
  | 4 => generatedGroup13
  | 5 => generatedGroup14
  | 6 => generatedGroup15
  | 7 => generatedGroup16

instance instGroupGeneratedFamilyPart02 :
    ∀ i, Group (generatedFamilyPart02 i)
  | 0 => inferInstanceAs (Group generatedGroup9)
  | 1 => inferInstanceAs (Group generatedGroup10)
  | 2 => inferInstanceAs (Group generatedGroup11)
  | 3 => inferInstanceAs (Group generatedGroup12)
  | 4 => inferInstanceAs (Group generatedGroup13)
  | 5 => inferInstanceAs (Group generatedGroup14)
  | 6 => inferInstanceAs (Group generatedGroup15)
  | 7 => inferInstanceAs (Group generatedGroup16)

theorem card_generatedFamilyPart02 :
    ∀ i, Nat.card (generatedFamilyPart02 i) = 32
  | 0 => card_generatedGroup9
  | 1 => card_generatedGroup10
  | 2 => card_generatedGroup11
  | 3 => card_generatedGroup12
  | 4 => card_generatedGroup13
  | 5 => card_generatedGroup14
  | 6 => card_generatedGroup15
  | 7 => card_generatedGroup16

abbrev generatedFamilyPart03 : Fin 8 → Type
  | 0 => generatedGroup17
  | 1 => generatedGroup18
  | 2 => generatedGroup19
  | 3 => generatedGroup20
  | 4 => generatedGroup21
  | 5 => generatedGroup22
  | 6 => generatedGroup23
  | 7 => generatedGroup24

instance instGroupGeneratedFamilyPart03 :
    ∀ i, Group (generatedFamilyPart03 i)
  | 0 => inferInstanceAs (Group generatedGroup17)
  | 1 => inferInstanceAs (Group generatedGroup18)
  | 2 => inferInstanceAs (Group generatedGroup19)
  | 3 => inferInstanceAs (Group generatedGroup20)
  | 4 => inferInstanceAs (Group generatedGroup21)
  | 5 => inferInstanceAs (Group generatedGroup22)
  | 6 => inferInstanceAs (Group generatedGroup23)
  | 7 => inferInstanceAs (Group generatedGroup24)

theorem card_generatedFamilyPart03 :
    ∀ i, Nat.card (generatedFamilyPart03 i) = 32
  | 0 => card_generatedGroup17
  | 1 => card_generatedGroup18
  | 2 => card_generatedGroup19
  | 3 => card_generatedGroup20
  | 4 => card_generatedGroup21
  | 5 => card_generatedGroup22
  | 6 => card_generatedGroup23
  | 7 => card_generatedGroup24

abbrev generatedFamilyPart04 : Fin 8 → Type
  | 0 => generatedGroup25
  | 1 => generatedGroup26
  | 2 => generatedGroup27
  | 3 => generatedGroup28
  | 4 => generatedGroup29
  | 5 => generatedGroup30
  | 6 => generatedGroup31
  | 7 => generatedGroup32

instance instGroupGeneratedFamilyPart04 :
    ∀ i, Group (generatedFamilyPart04 i)
  | 0 => inferInstanceAs (Group generatedGroup25)
  | 1 => inferInstanceAs (Group generatedGroup26)
  | 2 => inferInstanceAs (Group generatedGroup27)
  | 3 => inferInstanceAs (Group generatedGroup28)
  | 4 => inferInstanceAs (Group generatedGroup29)
  | 5 => inferInstanceAs (Group generatedGroup30)
  | 6 => inferInstanceAs (Group generatedGroup31)
  | 7 => inferInstanceAs (Group generatedGroup32)

theorem card_generatedFamilyPart04 :
    ∀ i, Nat.card (generatedFamilyPart04 i) = 32
  | 0 => card_generatedGroup25
  | 1 => card_generatedGroup26
  | 2 => card_generatedGroup27
  | 3 => card_generatedGroup28
  | 4 => card_generatedGroup29
  | 5 => card_generatedGroup30
  | 6 => card_generatedGroup31
  | 7 => card_generatedGroup32

abbrev generatedFamilyPart05 : Fin 8 → Type
  | 0 => generatedGroup33
  | 1 => generatedGroup34
  | 2 => generatedGroup35
  | 3 => generatedGroup36
  | 4 => generatedGroup37
  | 5 => generatedGroup38
  | 6 => generatedGroup39
  | 7 => generatedGroup40

instance instGroupGeneratedFamilyPart05 :
    ∀ i, Group (generatedFamilyPart05 i)
  | 0 => inferInstanceAs (Group generatedGroup33)
  | 1 => inferInstanceAs (Group generatedGroup34)
  | 2 => inferInstanceAs (Group generatedGroup35)
  | 3 => inferInstanceAs (Group generatedGroup36)
  | 4 => inferInstanceAs (Group generatedGroup37)
  | 5 => inferInstanceAs (Group generatedGroup38)
  | 6 => inferInstanceAs (Group generatedGroup39)
  | 7 => inferInstanceAs (Group generatedGroup40)

theorem card_generatedFamilyPart05 :
    ∀ i, Nat.card (generatedFamilyPart05 i) = 32
  | 0 => card_generatedGroup33
  | 1 => card_generatedGroup34
  | 2 => card_generatedGroup35
  | 3 => card_generatedGroup36
  | 4 => card_generatedGroup37
  | 5 => card_generatedGroup38
  | 6 => card_generatedGroup39
  | 7 => card_generatedGroup40

abbrev generatedFamilyPart06 : Fin 8 → Type
  | 0 => generatedGroup41
  | 1 => generatedGroup42
  | 2 => generatedGroup43
  | 3 => generatedGroup44
  | 4 => generatedGroup45
  | 5 => generatedGroup46
  | 6 => generatedGroup47
  | 7 => generatedGroup48

instance instGroupGeneratedFamilyPart06 :
    ∀ i, Group (generatedFamilyPart06 i)
  | 0 => inferInstanceAs (Group generatedGroup41)
  | 1 => inferInstanceAs (Group generatedGroup42)
  | 2 => inferInstanceAs (Group generatedGroup43)
  | 3 => inferInstanceAs (Group generatedGroup44)
  | 4 => inferInstanceAs (Group generatedGroup45)
  | 5 => inferInstanceAs (Group generatedGroup46)
  | 6 => inferInstanceAs (Group generatedGroup47)
  | 7 => inferInstanceAs (Group generatedGroup48)

theorem card_generatedFamilyPart06 :
    ∀ i, Nat.card (generatedFamilyPart06 i) = 32
  | 0 => card_generatedGroup41
  | 1 => card_generatedGroup42
  | 2 => card_generatedGroup43
  | 3 => card_generatedGroup44
  | 4 => card_generatedGroup45
  | 5 => card_generatedGroup46
  | 6 => card_generatedGroup47
  | 7 => card_generatedGroup48

abbrev generatedFamilyPart07 : Fin 3 → Type
  | 0 => generatedGroup49
  | 1 => generatedGroup50
  | 2 => generatedGroup51

instance instGroupGeneratedFamilyPart07 :
    ∀ i, Group (generatedFamilyPart07 i)
  | 0 => inferInstanceAs (Group generatedGroup49)
  | 1 => inferInstanceAs (Group generatedGroup50)
  | 2 => inferInstanceAs (Group generatedGroup51)

theorem card_generatedFamilyPart07 :
    ∀ i, Nat.card (generatedFamilyPart07 i) = 32
  | 0 => card_generatedGroup49
  | 1 => card_generatedGroup50
  | 2 => card_generatedGroup51

/-- The 51 generated central extensions, indexed by GAP id minus one. -/
def generatedFamily (i : Fin 51) : Type :=
  if h1 : i.1 < 8 then generatedFamilyPart01 ⟨i.1, h1⟩
  else if h2 : i.1 < 16 then generatedFamilyPart02 ⟨i.1 - 8, by omega⟩
  else if h3 : i.1 < 24 then generatedFamilyPart03 ⟨i.1 - 16, by omega⟩
  else if h4 : i.1 < 32 then generatedFamilyPart04 ⟨i.1 - 24, by omega⟩
  else if h5 : i.1 < 40 then generatedFamilyPart05 ⟨i.1 - 32, by omega⟩
  else if h6 : i.1 < 48 then generatedFamilyPart06 ⟨i.1 - 40, by omega⟩
  else generatedFamilyPart07 ⟨i.1 - 48, by omega⟩

instance instGroupGeneratedFamily (i : Fin 51) : Group (generatedFamily i) := by
  unfold generatedFamily
  split
  · infer_instance
  · split
    · infer_instance
    · split
      · infer_instance
      · split
        · infer_instance
        · split
          · infer_instance
          · split <;> infer_instance

theorem card_generatedFamily (i : Fin 51) : Nat.card (generatedFamily i) = 32 := by
  unfold generatedFamily
  split
  · exact card_generatedFamilyPart01 _
  · split
    · exact card_generatedFamilyPart02 _
    · split
      · exact card_generatedFamilyPart03 _
      · split
        · exact card_generatedFamilyPart04 _
        · split
          · exact card_generatedFamilyPart05 _
          · split
            · exact card_generatedFamilyPart06 _
            · exact card_generatedFamilyPart07 _

end Smallgroups.UsefulTheorems.Order32Certificate
