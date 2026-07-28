/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported

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
