/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported
import Smallgroups.GAP.Order32

/-!
# The unified accessor `smallGroup N j`

A single two-argument function encoding every GAP SmallGroups library isomorphism
class that has been imported so far:

* `smallPres N j : PCPres` — the pc presentation of `SmallGroup(N, j)`, dispatching
  to the imported presentations in `Polycyclic/Imported/`: the original prime-power
  range, all odd squarefree prime-pair orders at most `100`, and all orders `2p`
  with `p` an odd prime and `2p ≤ 100`.  Out-of-range or not-yet-imported pairs
  default to the trivial presentation `⟨[]⟩` (a junk value).
* `smallGroup N j : Type := PCGroup (smallPres N j)` — the group itself, with
  computable `Mul`/`One`/`Inv`/`Fintype`/`DecidableEq` and (on the imported range)
  a `Group` instance, all found by typeclass resolution since the definitions are
  `@[reducible]`.

When further orders are imported, extend the table in `smallPres` (the translator
`Scripts/translate_pc.py` regenerates the per-order files; the table is
hand-maintained for now).
-/

namespace Smallgroups.GAP

/-
/-- The 51 imported GAP presentations of order 32, indexed without an invalid case:
index `i : Fin 51` denotes `SmallGroup(32, i + 1)`. -/
@[reducible]
def smallPres32 : Fin 51 → PCPres
  | 0 => smallGroup_32_1
  | 1 => smallGroup_32_2
  | 2 => smallGroup_32_3
  | 3 => smallGroup_32_4
  | 4 => smallGroup_32_5
  | 5 => smallGroup_32_6
  | 6 => smallGroup_32_7
  | 7 => smallGroup_32_8
  | 8 => smallGroup_32_9
  | 9 => smallGroup_32_10
  | 10 => smallGroup_32_11
  | 11 => smallGroup_32_12
  | 12 => smallGroup_32_13
  | 13 => smallGroup_32_14
  | 14 => smallGroup_32_15
  | 15 => smallGroup_32_16
  | 16 => smallGroup_32_17
  | 17 => smallGroup_32_18
  | 18 => smallGroup_32_19
  | 19 => smallGroup_32_20
  | 20 => smallGroup_32_21
  | 21 => smallGroup_32_22
  | 22 => smallGroup_32_23
  | 23 => smallGroup_32_24
  | 24 => smallGroup_32_25
  | 25 => smallGroup_32_26
  | 26 => smallGroup_32_27
  | 27 => smallGroup_32_28
  | 28 => smallGroup_32_29
  | 29 => smallGroup_32_30
  | 30 => smallGroup_32_31
  | 31 => smallGroup_32_32
  | 32 => smallGroup_32_33
  | 33 => smallGroup_32_34
  | 34 => smallGroup_32_35
  | 35 => smallGroup_32_36
  | 36 => smallGroup_32_37
  | 37 => smallGroup_32_38
  | 38 => smallGroup_32_39
  | 39 => smallGroup_32_40
  | 40 => smallGroup_32_41
  | 41 => smallGroup_32_42
  | 42 => smallGroup_32_43
  | 43 => smallGroup_32_44
  | 44 => smallGroup_32_45
  | 45 => smallGroup_32_46
  | 46 => smallGroup_32_47
  | 47 => smallGroup_32_48
  | 48 => smallGroup_32_49
  | 49 => smallGroup_32_50
  | 50 => smallGroup_32_51

/-- The GAP-numbered order-32 groups.  Unlike the legacy two-natural-number
dispatcher, this family has no out-of-range fallback. -/
@[reducible]
def smallGroup32 (i : Fin 51) : Type := PCGroup (smallPres32 i)

instance instGroupSmallGroup32 : ∀ i : Fin 51, Group (smallGroup32 i)
  | 0 => inferInstanceAs (Group (PCGroup smallGroup_32_1))
  | 1 => inferInstanceAs (Group (PCGroup smallGroup_32_2))
  | 2 => inferInstanceAs (Group (PCGroup smallGroup_32_3))
  | 3 => inferInstanceAs (Group (PCGroup smallGroup_32_4))
  | 4 => inferInstanceAs (Group (PCGroup smallGroup_32_5))
  | 5 => inferInstanceAs (Group (PCGroup smallGroup_32_6))
  | 6 => inferInstanceAs (Group (PCGroup smallGroup_32_7))
  | 7 => inferInstanceAs (Group (PCGroup smallGroup_32_8))
  | 8 => inferInstanceAs (Group (PCGroup smallGroup_32_9))
  | 9 => inferInstanceAs (Group (PCGroup smallGroup_32_10))
  | 10 => inferInstanceAs (Group (PCGroup smallGroup_32_11))
  | 11 => inferInstanceAs (Group (PCGroup smallGroup_32_12))
  | 12 => inferInstanceAs (Group (PCGroup smallGroup_32_13))
  | 13 => inferInstanceAs (Group (PCGroup smallGroup_32_14))
  | 14 => inferInstanceAs (Group (PCGroup smallGroup_32_15))
  | 15 => inferInstanceAs (Group (PCGroup smallGroup_32_16))
  | 16 => inferInstanceAs (Group (PCGroup smallGroup_32_17))
  | 17 => inferInstanceAs (Group (PCGroup smallGroup_32_18))
  | 18 => inferInstanceAs (Group (PCGroup smallGroup_32_19))
  | 19 => inferInstanceAs (Group (PCGroup smallGroup_32_20))
  | 20 => inferInstanceAs (Group (PCGroup smallGroup_32_21))
  | 21 => inferInstanceAs (Group (PCGroup smallGroup_32_22))
  | 22 => inferInstanceAs (Group (PCGroup smallGroup_32_23))
  | 23 => inferInstanceAs (Group (PCGroup smallGroup_32_24))
  | 24 => inferInstanceAs (Group (PCGroup smallGroup_32_25))
  | 25 => inferInstanceAs (Group (PCGroup smallGroup_32_26))
  | 26 => inferInstanceAs (Group (PCGroup smallGroup_32_27))
  | 27 => inferInstanceAs (Group (PCGroup smallGroup_32_28))
  | 28 => inferInstanceAs (Group (PCGroup smallGroup_32_29))
  | 29 => inferInstanceAs (Group (PCGroup smallGroup_32_30))
  | 30 => inferInstanceAs (Group (PCGroup smallGroup_32_31))
  | 31 => inferInstanceAs (Group (PCGroup smallGroup_32_32))
  | 32 => inferInstanceAs (Group (PCGroup smallGroup_32_33))
  | 33 => inferInstanceAs (Group (PCGroup smallGroup_32_34))
  | 34 => inferInstanceAs (Group (PCGroup smallGroup_32_35))
  | 35 => inferInstanceAs (Group (PCGroup smallGroup_32_36))
  | 36 => inferInstanceAs (Group (PCGroup smallGroup_32_37))
  | 37 => inferInstanceAs (Group (PCGroup smallGroup_32_38))
  | 38 => inferInstanceAs (Group (PCGroup smallGroup_32_39))
  | 39 => inferInstanceAs (Group (PCGroup smallGroup_32_40))
  | 40 => inferInstanceAs (Group (PCGroup smallGroup_32_41))
  | 41 => inferInstanceAs (Group (PCGroup smallGroup_32_42))
  | 42 => inferInstanceAs (Group (PCGroup smallGroup_32_43))
  | 43 => inferInstanceAs (Group (PCGroup smallGroup_32_44))
  | 44 => inferInstanceAs (Group (PCGroup smallGroup_32_45))
  | 45 => inferInstanceAs (Group (PCGroup smallGroup_32_46))
  | 46 => inferInstanceAs (Group (PCGroup smallGroup_32_47))
  | 47 => inferInstanceAs (Group (PCGroup smallGroup_32_48))
  | 48 => inferInstanceAs (Group (PCGroup smallGroup_32_49))
  | 49 => inferInstanceAs (Group (PCGroup smallGroup_32_50))
  | 50 => inferInstanceAs (Group (PCGroup smallGroup_32_51))

theorem card_smallGroup32 : ∀ i : Fin 51, Nat.card (smallGroup32 i) = 32
  | 0 => card_smallGroup_32_1
  | 1 => card_smallGroup_32_2
  | 2 => card_smallGroup_32_3
  | 3 => card_smallGroup_32_4
  | 4 => card_smallGroup_32_5
  | 5 => card_smallGroup_32_6
  | 6 => card_smallGroup_32_7
  | 7 => card_smallGroup_32_8
  | 8 => card_smallGroup_32_9
  | 9 => card_smallGroup_32_10
  | 10 => card_smallGroup_32_11
  | 11 => card_smallGroup_32_12
  | 12 => card_smallGroup_32_13
  | 13 => card_smallGroup_32_14
  | 14 => card_smallGroup_32_15
  | 15 => card_smallGroup_32_16
  | 16 => card_smallGroup_32_17
  | 17 => card_smallGroup_32_18
  | 18 => card_smallGroup_32_19
  | 19 => card_smallGroup_32_20
  | 20 => card_smallGroup_32_21
  | 21 => card_smallGroup_32_22
  | 22 => card_smallGroup_32_23
  | 23 => card_smallGroup_32_24
  | 24 => card_smallGroup_32_25
  | 25 => card_smallGroup_32_26
  | 26 => card_smallGroup_32_27
  | 27 => card_smallGroup_32_28
  | 28 => card_smallGroup_32_29
  | 29 => card_smallGroup_32_30
  | 30 => card_smallGroup_32_31
  | 31 => card_smallGroup_32_32
  | 32 => card_smallGroup_32_33
  | 33 => card_smallGroup_32_34
  | 34 => card_smallGroup_32_35
  | 35 => card_smallGroup_32_36
  | 36 => card_smallGroup_32_37
  | 37 => card_smallGroup_32_38
  | 38 => card_smallGroup_32_39
  | 39 => card_smallGroup_32_40
  | 40 => card_smallGroup_32_41
  | 41 => card_smallGroup_32_42
  | 42 => card_smallGroup_32_43
  | 43 => card_smallGroup_32_44
  | 44 => card_smallGroup_32_45
  | 45 => card_smallGroup_32_46
  | 46 => card_smallGroup_32_47
  | 47 => card_smallGroup_32_48
  | 48 => card_smallGroup_32_49
  | 49 => card_smallGroup_32_50
  | 50 => card_smallGroup_32_51
-/

/-- The pc presentation of `SmallGroup(N, j)`, for the imported orders.
Out-of-range or not-yet-imported pairs default to the trivial presentation. -/
@[reducible]
def smallPres : ℕ → ℕ → PCPres
  | 1, 1 => smallGroup_1_1
  | 2, 1 => smallGroup_2_1
  | 4, 1 => smallGroup_4_1
  | 4, 2 => smallGroup_4_2
  | 6, 1 => smallGroup_6_1
  | 6, 2 => smallGroup_6_2
  | 8, 1 => smallGroup_8_1
  | 8, 2 => smallGroup_8_2
  | 8, 3 => smallGroup_8_3
  | 8, 4 => smallGroup_8_4
  | 8, 5 => smallGroup_8_5
  | 10, 1 => smallGroup_10_1
  | 10, 2 => smallGroup_10_2
  | 16, 1 => smallGroup_16_1
  | 16, 2 => smallGroup_16_2
  | 16, 3 => smallGroup_16_3
  | 16, 4 => smallGroup_16_4
  | 16, 5 => smallGroup_16_5
  | 16, 6 => smallGroup_16_6
  | 16, 7 => smallGroup_16_7
  | 16, 8 => smallGroup_16_8
  | 16, 9 => smallGroup_16_9
  | 16, 10 => smallGroup_16_10
  | 16, 11 => smallGroup_16_11
  | 16, 12 => smallGroup_16_12
  | 16, 13 => smallGroup_16_13
  | 16, 14 => smallGroup_16_14
  | 25, 1 => smallGroup_25_1
  | 25, 2 => smallGroup_25_2
  | 27, 1 => smallGroup_27_1
  | 27, 2 => smallGroup_27_2
  | 27, 3 => smallGroup_27_3
  | 27, 4 => smallGroup_27_4
  | 27, 5 => smallGroup_27_5
  | 32, 1 => smallGroup_32_1
  | 32, 2 => smallGroup_32_2
  | 32, 3 => smallGroup_32_3
  | 32, 4 => smallGroup_32_4
  | 32, 5 => smallGroup_32_5
  | 32, 6 => smallGroup_32_6
  | 32, 7 => smallGroup_32_7
  | 32, 8 => smallGroup_32_8
  | 32, 9 => smallGroup_32_9
  | 32, 10 => smallGroup_32_10
  | 32, 11 => smallGroup_32_11
  | 32, 12 => smallGroup_32_12
  | 32, 13 => smallGroup_32_13
  | 32, 14 => smallGroup_32_14
  | 32, 15 => smallGroup_32_15
  | 32, 16 => smallGroup_32_16
  | 32, 17 => smallGroup_32_17
  | 32, 18 => smallGroup_32_18
  | 32, 19 => smallGroup_32_19
  | 32, 20 => smallGroup_32_20
  | 32, 21 => smallGroup_32_21
  | 32, 22 => smallGroup_32_22
  | 32, 23 => smallGroup_32_23
  | 32, 24 => smallGroup_32_24
  | 32, 25 => smallGroup_32_25
  | 32, 26 => smallGroup_32_26
  | 32, 27 => smallGroup_32_27
  | 32, 28 => smallGroup_32_28
  | 32, 29 => smallGroup_32_29
  | 32, 30 => smallGroup_32_30
  | 32, 31 => smallGroup_32_31
  | 32, 32 => smallGroup_32_32
  | 32, 33 => smallGroup_32_33
  | 32, 34 => smallGroup_32_34
  | 32, 35 => smallGroup_32_35
  | 32, 36 => smallGroup_32_36
  | 32, 37 => smallGroup_32_37
  | 32, 38 => smallGroup_32_38
  | 32, 39 => smallGroup_32_39
  | 32, 40 => smallGroup_32_40
  | 32, 41 => smallGroup_32_41
  | 32, 42 => smallGroup_32_42
  | 32, 43 => smallGroup_32_43
  | 32, 44 => smallGroup_32_44
  | 32, 45 => smallGroup_32_45
  | 32, 46 => smallGroup_32_46
  | 32, 47 => smallGroup_32_47
  | 32, 48 => smallGroup_32_48
  | 32, 49 => smallGroup_32_49
  | 32, 50 => smallGroup_32_50
  | 32, 51 => smallGroup_32_51
  | 9, 1 => smallGroup_9_1
  | 9, 2 => smallGroup_9_2
  | 49, 1 => smallGroup_49_1
  | 49, 2 => smallGroup_49_2
  | 14, 1 => smallGroup_14_1
  | 14, 2 => smallGroup_14_2
  | 15, 1 => smallGroup_15_1
  | 21, 1 => smallGroup_21_1
  | 21, 2 => smallGroup_21_2
  | 22, 1 => smallGroup_22_1
  | 22, 2 => smallGroup_22_2
  | 26, 1 => smallGroup_26_1
  | 26, 2 => smallGroup_26_2
  | 33, 1 => smallGroup_33_1
  | 34, 1 => smallGroup_34_1
  | 34, 2 => smallGroup_34_2
  | 35, 1 => smallGroup_35_1
  | 38, 1 => smallGroup_38_1
  | 38, 2 => smallGroup_38_2
  | 39, 1 => smallGroup_39_1
  | 39, 2 => smallGroup_39_2
  | 46, 1 => smallGroup_46_1
  | 46, 2 => smallGroup_46_2
  | 51, 1 => smallGroup_51_1
  | 55, 1 => smallGroup_55_1
  | 55, 2 => smallGroup_55_2
  | 57, 1 => smallGroup_57_1
  | 57, 2 => smallGroup_57_2
  | 58, 1 => smallGroup_58_1
  | 58, 2 => smallGroup_58_2
  | 62, 1 => smallGroup_62_1
  | 62, 2 => smallGroup_62_2
  | 65, 1 => smallGroup_65_1
  | 69, 1 => smallGroup_69_1
  | 74, 1 => smallGroup_74_1
  | 74, 2 => smallGroup_74_2
  | 77, 1 => smallGroup_77_1
  | 82, 1 => smallGroup_82_1
  | 82, 2 => smallGroup_82_2
  | 85, 1 => smallGroup_85_1
  | 86, 1 => smallGroup_86_1
  | 86, 2 => smallGroup_86_2
  | 87, 1 => smallGroup_87_1
  | 91, 1 => smallGroup_91_1
  | 93, 1 => smallGroup_93_1
  | 93, 2 => smallGroup_93_2
  | 94, 1 => smallGroup_94_1
  | 94, 2 => smallGroup_94_2
  | 95, 1 => smallGroup_95_1
  | _, _ => smallGroup_1_1

/-- The GAP SmallGroups library group `SmallGroup(N, j)`, for the imported orders. -/
@[reducible]
def smallGroup (N j : ℕ) : Type := PCGroup (smallPres N j)

/-! The `Group` instances for the imported range.  The `@[reducible]` dispatcher
does not unfold during typeclass resolution (the literal match is stuck), so each
imported pair gets an explicit instance; the per-order files already provide
`Group (PCGroup smallGroup_N_j)`. -/

instance : Group (smallGroup 1 1) := inferInstanceAs (Group PUnit)
instance : Group (smallGroup 2 1) := inferInstanceAs (Group (PCGroup smallGroup_2_1))
instance : Group (smallGroup 4 1) := inferInstanceAs (Group (PCGroup smallGroup_4_1))
instance : Group (smallGroup 4 2) := inferInstanceAs (Group (PCGroup smallGroup_4_2))
instance : Group (smallGroup 6 1) := inferInstanceAs (Group (PCGroup smallGroup_6_1))
instance : Group (smallGroup 6 2) := inferInstanceAs (Group (PCGroup smallGroup_6_2))
instance : Group (smallGroup 8 1) := inferInstanceAs (Group (PCGroup smallGroup_8_1))
instance : Group (smallGroup 8 2) := inferInstanceAs (Group (PCGroup smallGroup_8_2))
instance : Group (smallGroup 8 3) := inferInstanceAs (Group (PCGroup smallGroup_8_3))
instance : Group (smallGroup 8 4) := inferInstanceAs (Group (PCGroup smallGroup_8_4))
instance : Group (smallGroup 8 5) := inferInstanceAs (Group (PCGroup smallGroup_8_5))
instance : Group (smallGroup 10 1) := inferInstanceAs (Group (PCGroup smallGroup_10_1))
instance : Group (smallGroup 10 2) := inferInstanceAs (Group (PCGroup smallGroup_10_2))
instance : Group (smallGroup 16 1) := inferInstanceAs (Group (PCGroup smallGroup_16_1))
instance : Group (smallGroup 16 2) := inferInstanceAs (Group (PCGroup smallGroup_16_2))
instance : Group (smallGroup 16 3) := inferInstanceAs (Group (PCGroup smallGroup_16_3))
instance : Group (smallGroup 16 4) := inferInstanceAs (Group (PCGroup smallGroup_16_4))
instance : Group (smallGroup 16 5) := inferInstanceAs (Group (PCGroup smallGroup_16_5))
instance : Group (smallGroup 16 6) := inferInstanceAs (Group (PCGroup smallGroup_16_6))
instance : Group (smallGroup 16 7) := inferInstanceAs (Group (PCGroup smallGroup_16_7))
instance : Group (smallGroup 16 8) := inferInstanceAs (Group (PCGroup smallGroup_16_8))
instance : Group (smallGroup 16 9) := inferInstanceAs (Group (PCGroup smallGroup_16_9))
instance : Group (smallGroup 16 10) := inferInstanceAs (Group (PCGroup smallGroup_16_10))
instance : Group (smallGroup 16 11) := inferInstanceAs (Group (PCGroup smallGroup_16_11))
instance : Group (smallGroup 16 12) := inferInstanceAs (Group (PCGroup smallGroup_16_12))
instance : Group (smallGroup 16 13) := inferInstanceAs (Group (PCGroup smallGroup_16_13))
instance : Group (smallGroup 16 14) := inferInstanceAs (Group (PCGroup smallGroup_16_14))
instance : Group (smallGroup 25 1) := inferInstanceAs (Group (PCGroup smallGroup_25_1))
instance : Group (smallGroup 25 2) := inferInstanceAs (Group (PCGroup smallGroup_25_2))
instance : Group (smallGroup 27 1) := inferInstanceAs (Group (PCGroup smallGroup_27_1))
instance : Group (smallGroup 27 2) := inferInstanceAs (Group (PCGroup smallGroup_27_2))
instance : Group (smallGroup 27 3) := inferInstanceAs (Group (PCGroup smallGroup_27_3))
instance : Group (smallGroup 27 4) := inferInstanceAs (Group (PCGroup smallGroup_27_4))
instance : Group (smallGroup 27 5) := inferInstanceAs (Group (PCGroup smallGroup_27_5))
instance : Group (smallGroup 9 1) := inferInstanceAs (Group (PCGroup smallGroup_9_1))
instance : Group (smallGroup 9 2) := inferInstanceAs (Group (PCGroup smallGroup_9_2))
instance : Group (smallGroup 49 1) := inferInstanceAs (Group (PCGroup smallGroup_49_1))
instance : Group (smallGroup 49 2) := inferInstanceAs (Group (PCGroup smallGroup_49_2))
instance : Group (smallGroup 14 1) := inferInstanceAs (Group (PCGroup smallGroup_14_1))
instance : Group (smallGroup 14 2) := inferInstanceAs (Group (PCGroup smallGroup_14_2))
instance : Group (smallGroup 15 1) := inferInstanceAs (Group (PCGroup smallGroup_15_1))
instance : Group (smallGroup 21 1) := inferInstanceAs (Group (PCGroup smallGroup_21_1))
instance : Group (smallGroup 21 2) := inferInstanceAs (Group (PCGroup smallGroup_21_2))
instance : Group (smallGroup 22 1) := inferInstanceAs (Group (PCGroup smallGroup_22_1))
instance : Group (smallGroup 22 2) := inferInstanceAs (Group (PCGroup smallGroup_22_2))
instance : Group (smallGroup 26 1) := inferInstanceAs (Group (PCGroup smallGroup_26_1))
instance : Group (smallGroup 26 2) := inferInstanceAs (Group (PCGroup smallGroup_26_2))
instance : Group (smallGroup 33 1) := inferInstanceAs (Group (PCGroup smallGroup_33_1))
instance : Group (smallGroup 34 1) := inferInstanceAs (Group (PCGroup smallGroup_34_1))
instance : Group (smallGroup 34 2) := inferInstanceAs (Group (PCGroup smallGroup_34_2))
instance : Group (smallGroup 35 1) := inferInstanceAs (Group (PCGroup smallGroup_35_1))
instance : Group (smallGroup 38 1) := inferInstanceAs (Group (PCGroup smallGroup_38_1))
instance : Group (smallGroup 38 2) := inferInstanceAs (Group (PCGroup smallGroup_38_2))
instance : Group (smallGroup 39 1) := inferInstanceAs (Group (PCGroup smallGroup_39_1))
instance : Group (smallGroup 39 2) := inferInstanceAs (Group (PCGroup smallGroup_39_2))
instance : Group (smallGroup 46 1) := inferInstanceAs (Group (PCGroup smallGroup_46_1))
instance : Group (smallGroup 46 2) := inferInstanceAs (Group (PCGroup smallGroup_46_2))
instance : Group (smallGroup 51 1) := inferInstanceAs (Group (PCGroup smallGroup_51_1))
instance : Group (smallGroup 55 1) := inferInstanceAs (Group (PCGroup smallGroup_55_1))
instance : Group (smallGroup 55 2) := inferInstanceAs (Group (PCGroup smallGroup_55_2))
instance : Group (smallGroup 57 1) := inferInstanceAs (Group (PCGroup smallGroup_57_1))
instance : Group (smallGroup 57 2) := inferInstanceAs (Group (PCGroup smallGroup_57_2))
instance : Group (smallGroup 58 1) := inferInstanceAs (Group (PCGroup smallGroup_58_1))
instance : Group (smallGroup 58 2) := inferInstanceAs (Group (PCGroup smallGroup_58_2))
instance : Group (smallGroup 62 1) := inferInstanceAs (Group (PCGroup smallGroup_62_1))
instance : Group (smallGroup 62 2) := inferInstanceAs (Group (PCGroup smallGroup_62_2))
instance : Group (smallGroup 65 1) := inferInstanceAs (Group (PCGroup smallGroup_65_1))
instance : Group (smallGroup 69 1) := inferInstanceAs (Group (PCGroup smallGroup_69_1))
instance : Group (smallGroup 74 1) := inferInstanceAs (Group (PCGroup smallGroup_74_1))
instance : Group (smallGroup 74 2) := inferInstanceAs (Group (PCGroup smallGroup_74_2))
instance : Group (smallGroup 77 1) := inferInstanceAs (Group (PCGroup smallGroup_77_1))
instance : Group (smallGroup 82 1) := inferInstanceAs (Group (PCGroup smallGroup_82_1))
instance : Group (smallGroup 82 2) := inferInstanceAs (Group (PCGroup smallGroup_82_2))
instance : Group (smallGroup 85 1) := inferInstanceAs (Group (PCGroup smallGroup_85_1))
instance : Group (smallGroup 86 1) := inferInstanceAs (Group (PCGroup smallGroup_86_1))
instance : Group (smallGroup 86 2) := inferInstanceAs (Group (PCGroup smallGroup_86_2))
instance : Group (smallGroup 87 1) := inferInstanceAs (Group (PCGroup smallGroup_87_1))
instance : Group (smallGroup 91 1) := inferInstanceAs (Group (PCGroup smallGroup_91_1))
instance : Group (smallGroup 93 1) := inferInstanceAs (Group (PCGroup smallGroup_93_1))
instance : Group (smallGroup 93 2) := inferInstanceAs (Group (PCGroup smallGroup_93_2))
instance : Group (smallGroup 94 1) := inferInstanceAs (Group (PCGroup smallGroup_94_1))
instance : Group (smallGroup 94 2) := inferInstanceAs (Group (PCGroup smallGroup_94_2))
instance : Group (smallGroup 95 1) := inferInstanceAs (Group (PCGroup smallGroup_95_1))

end Smallgroups.GAP
