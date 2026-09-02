/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Mathlib.Tactic

/-!
# GAP-numbered groups of order 32

This module gives a total, fallback-free family indexed by `Fin 51`.  Seven
small internal families mirror the generated pc-presentation chunks while
keeping pattern matching and typeclass synthesis inexpensive.
-/

namespace Smallgroups.GAP

@[reducible] def smallPres32Part01 : Fin 8 → PCPres
  | 0 => smallGroup_32_1
  | 1 => smallGroup_32_2
  | 2 => smallGroup_32_3
  | 3 => smallGroup_32_4
  | 4 => smallGroup_32_5
  | 5 => smallGroup_32_6
  | 6 => smallGroup_32_7
  | 7 => smallGroup_32_8

instance instGroupSmallPres32Part01 : ∀ i, Group (PCGroup (smallPres32Part01 i))
  | 0 => inferInstanceAs (Group (PCGroup smallGroup_32_1))
  | 1 => inferInstanceAs (Group (PCGroup smallGroup_32_2))
  | 2 => inferInstanceAs (Group (PCGroup smallGroup_32_3))
  | 3 => inferInstanceAs (Group (PCGroup smallGroup_32_4))
  | 4 => inferInstanceAs (Group (PCGroup smallGroup_32_5))
  | 5 => inferInstanceAs (Group (PCGroup smallGroup_32_6))
  | 6 => inferInstanceAs (Group (PCGroup smallGroup_32_7))
  | 7 => inferInstanceAs (Group (PCGroup smallGroup_32_8))

theorem card_smallPres32Part01 : ∀ i, Nat.card (PCGroup (smallPres32Part01 i)) = 32
  | 0 => card_smallGroup_32_1
  | 1 => card_smallGroup_32_2
  | 2 => card_smallGroup_32_3
  | 3 => card_smallGroup_32_4
  | 4 => card_smallGroup_32_5
  | 5 => card_smallGroup_32_6
  | 6 => card_smallGroup_32_7
  | 7 => card_smallGroup_32_8

@[reducible] def smallPres32Part02 : Fin 8 → PCPres
  | 0 => smallGroup_32_9
  | 1 => smallGroup_32_10
  | 2 => smallGroup_32_11
  | 3 => smallGroup_32_12
  | 4 => smallGroup_32_13
  | 5 => smallGroup_32_14
  | 6 => smallGroup_32_15
  | 7 => smallGroup_32_16

instance instGroupSmallPres32Part02 : ∀ i, Group (PCGroup (smallPres32Part02 i))
  | 0 => inferInstanceAs (Group (PCGroup smallGroup_32_9))
  | 1 => inferInstanceAs (Group (PCGroup smallGroup_32_10))
  | 2 => inferInstanceAs (Group (PCGroup smallGroup_32_11))
  | 3 => inferInstanceAs (Group (PCGroup smallGroup_32_12))
  | 4 => inferInstanceAs (Group (PCGroup smallGroup_32_13))
  | 5 => inferInstanceAs (Group (PCGroup smallGroup_32_14))
  | 6 => inferInstanceAs (Group (PCGroup smallGroup_32_15))
  | 7 => inferInstanceAs (Group (PCGroup smallGroup_32_16))

theorem card_smallPres32Part02 : ∀ i, Nat.card (PCGroup (smallPres32Part02 i)) = 32
  | 0 => card_smallGroup_32_9
  | 1 => card_smallGroup_32_10
  | 2 => card_smallGroup_32_11
  | 3 => card_smallGroup_32_12
  | 4 => card_smallGroup_32_13
  | 5 => card_smallGroup_32_14
  | 6 => card_smallGroup_32_15
  | 7 => card_smallGroup_32_16

@[reducible] def smallPres32Part03 : Fin 8 → PCPres
  | 0 => smallGroup_32_17
  | 1 => smallGroup_32_18
  | 2 => smallGroup_32_19
  | 3 => smallGroup_32_20
  | 4 => smallGroup_32_21
  | 5 => smallGroup_32_22
  | 6 => smallGroup_32_23
  | 7 => smallGroup_32_24

instance instGroupSmallPres32Part03 : ∀ i, Group (PCGroup (smallPres32Part03 i))
  | 0 => inferInstanceAs (Group (PCGroup smallGroup_32_17))
  | 1 => inferInstanceAs (Group (PCGroup smallGroup_32_18))
  | 2 => inferInstanceAs (Group (PCGroup smallGroup_32_19))
  | 3 => inferInstanceAs (Group (PCGroup smallGroup_32_20))
  | 4 => inferInstanceAs (Group (PCGroup smallGroup_32_21))
  | 5 => inferInstanceAs (Group (PCGroup smallGroup_32_22))
  | 6 => inferInstanceAs (Group (PCGroup smallGroup_32_23))
  | 7 => inferInstanceAs (Group (PCGroup smallGroup_32_24))

theorem card_smallPres32Part03 : ∀ i, Nat.card (PCGroup (smallPres32Part03 i)) = 32
  | 0 => card_smallGroup_32_17
  | 1 => card_smallGroup_32_18
  | 2 => card_smallGroup_32_19
  | 3 => card_smallGroup_32_20
  | 4 => card_smallGroup_32_21
  | 5 => card_smallGroup_32_22
  | 6 => card_smallGroup_32_23
  | 7 => card_smallGroup_32_24

@[reducible] def smallPres32Part04 : Fin 8 → PCPres
  | 0 => smallGroup_32_25
  | 1 => smallGroup_32_26
  | 2 => smallGroup_32_27
  | 3 => smallGroup_32_28
  | 4 => smallGroup_32_29
  | 5 => smallGroup_32_30
  | 6 => smallGroup_32_31
  | 7 => smallGroup_32_32

instance instGroupSmallPres32Part04 : ∀ i, Group (PCGroup (smallPres32Part04 i))
  | 0 => inferInstanceAs (Group (PCGroup smallGroup_32_25))
  | 1 => inferInstanceAs (Group (PCGroup smallGroup_32_26))
  | 2 => inferInstanceAs (Group (PCGroup smallGroup_32_27))
  | 3 => inferInstanceAs (Group (PCGroup smallGroup_32_28))
  | 4 => inferInstanceAs (Group (PCGroup smallGroup_32_29))
  | 5 => inferInstanceAs (Group (PCGroup smallGroup_32_30))
  | 6 => inferInstanceAs (Group (PCGroup smallGroup_32_31))
  | 7 => inferInstanceAs (Group (PCGroup smallGroup_32_32))

theorem card_smallPres32Part04 : ∀ i, Nat.card (PCGroup (smallPres32Part04 i)) = 32
  | 0 => card_smallGroup_32_25
  | 1 => card_smallGroup_32_26
  | 2 => card_smallGroup_32_27
  | 3 => card_smallGroup_32_28
  | 4 => card_smallGroup_32_29
  | 5 => card_smallGroup_32_30
  | 6 => card_smallGroup_32_31
  | 7 => card_smallGroup_32_32

@[reducible] def smallPres32Part05 : Fin 8 → PCPres
  | 0 => smallGroup_32_33
  | 1 => smallGroup_32_34
  | 2 => smallGroup_32_35
  | 3 => smallGroup_32_36
  | 4 => smallGroup_32_37
  | 5 => smallGroup_32_38
  | 6 => smallGroup_32_39
  | 7 => smallGroup_32_40

instance instGroupSmallPres32Part05 : ∀ i, Group (PCGroup (smallPres32Part05 i))
  | 0 => inferInstanceAs (Group (PCGroup smallGroup_32_33))
  | 1 => inferInstanceAs (Group (PCGroup smallGroup_32_34))
  | 2 => inferInstanceAs (Group (PCGroup smallGroup_32_35))
  | 3 => inferInstanceAs (Group (PCGroup smallGroup_32_36))
  | 4 => inferInstanceAs (Group (PCGroup smallGroup_32_37))
  | 5 => inferInstanceAs (Group (PCGroup smallGroup_32_38))
  | 6 => inferInstanceAs (Group (PCGroup smallGroup_32_39))
  | 7 => inferInstanceAs (Group (PCGroup smallGroup_32_40))

theorem card_smallPres32Part05 : ∀ i, Nat.card (PCGroup (smallPres32Part05 i)) = 32
  | 0 => card_smallGroup_32_33
  | 1 => card_smallGroup_32_34
  | 2 => card_smallGroup_32_35
  | 3 => card_smallGroup_32_36
  | 4 => card_smallGroup_32_37
  | 5 => card_smallGroup_32_38
  | 6 => card_smallGroup_32_39
  | 7 => card_smallGroup_32_40

@[reducible] def smallPres32Part06 : Fin 8 → PCPres
  | 0 => smallGroup_32_41
  | 1 => smallGroup_32_42
  | 2 => smallGroup_32_43
  | 3 => smallGroup_32_44
  | 4 => smallGroup_32_45
  | 5 => smallGroup_32_46
  | 6 => smallGroup_32_47
  | 7 => smallGroup_32_48

instance instGroupSmallPres32Part06 : ∀ i, Group (PCGroup (smallPres32Part06 i))
  | 0 => inferInstanceAs (Group (PCGroup smallGroup_32_41))
  | 1 => inferInstanceAs (Group (PCGroup smallGroup_32_42))
  | 2 => inferInstanceAs (Group (PCGroup smallGroup_32_43))
  | 3 => inferInstanceAs (Group (PCGroup smallGroup_32_44))
  | 4 => inferInstanceAs (Group (PCGroup smallGroup_32_45))
  | 5 => inferInstanceAs (Group (PCGroup smallGroup_32_46))
  | 6 => inferInstanceAs (Group (PCGroup smallGroup_32_47))
  | 7 => inferInstanceAs (Group (PCGroup smallGroup_32_48))

theorem card_smallPres32Part06 : ∀ i, Nat.card (PCGroup (smallPres32Part06 i)) = 32
  | 0 => card_smallGroup_32_41
  | 1 => card_smallGroup_32_42
  | 2 => card_smallGroup_32_43
  | 3 => card_smallGroup_32_44
  | 4 => card_smallGroup_32_45
  | 5 => card_smallGroup_32_46
  | 6 => card_smallGroup_32_47
  | 7 => card_smallGroup_32_48

@[reducible] def smallPres32Part07 : Fin 3 → PCPres
  | 0 => smallGroup_32_49
  | 1 => smallGroup_32_50
  | 2 => smallGroup_32_51

instance instGroupSmallPres32Part07 : ∀ i, Group (PCGroup (smallPres32Part07 i))
  | 0 => inferInstanceAs (Group (PCGroup smallGroup_32_49))
  | 1 => inferInstanceAs (Group (PCGroup smallGroup_32_50))
  | 2 => inferInstanceAs (Group (PCGroup smallGroup_32_51))

theorem card_smallPres32Part07 : ∀ i, Nat.card (PCGroup (smallPres32Part07 i)) = 32
  | 0 => card_smallGroup_32_49
  | 1 => card_smallGroup_32_50
  | 2 => card_smallGroup_32_51

/-- The 51 imported GAP presentations of order 32.  Index `i` denotes
`SmallGroup(32, i + 1)`. -/
def smallPres32 (i : Fin 51) : PCPres :=
  if h1 : i.1 < 8 then
    smallPres32Part01 ⟨i.1, by omega⟩
  else
  if h2 : i.1 < 16 then
    smallPres32Part02 ⟨i.1 - 8, by omega⟩
  else
  if h3 : i.1 < 24 then
    smallPres32Part03 ⟨i.1 - 16, by omega⟩
  else
  if h4 : i.1 < 32 then
    smallPres32Part04 ⟨i.1 - 24, by omega⟩
  else
  if h5 : i.1 < 40 then
    smallPres32Part05 ⟨i.1 - 32, by omega⟩
  else
  if h6 : i.1 < 48 then
    smallPres32Part06 ⟨i.1 - 40, by omega⟩
  else
    smallPres32Part07 ⟨i.1 - 48, by omega⟩

/-- The fallback-free GAP-numbered family of groups of order 32. -/
def smallGroup32 (i : Fin 51) : Type := PCGroup (smallPres32 i)

instance instGroupSmallGroup32 (i : Fin 51) : Group (smallGroup32 i) := by
  unfold smallGroup32 smallPres32
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

theorem card_smallGroup32 (i : Fin 51) : Nat.card (smallGroup32 i) = 32 := by
  unfold smallGroup32 smallPres32
  split
  · exact card_smallPres32Part01 _
  · split
    · exact card_smallPres32Part02 _
    · split
      · exact card_smallPres32Part03 _
      · split
        · exact card_smallPres32Part04 _
        · split
          · exact card_smallPres32Part05 _
          · split
            · exact card_smallPres32Part06 _
            · exact card_smallPres32Part07 _

end Smallgroups.GAP
