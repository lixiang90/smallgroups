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
  to the imported presentations in `Polycyclic/Imported/` (orders `1, 2, 8, 16, 27`
  so far).  Out-of-range or not-yet-imported pairs default to the trivial
  presentation `⟨[]⟩` (a junk value; only the imported range is meant to be used).
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
  | 8, 1 => smallGroup_8_1
  | 8, 2 => smallGroup_8_2
  | 8, 3 => smallGroup_8_3
  | 8, 4 => smallGroup_8_4
  | 8, 5 => smallGroup_8_5
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
instance : Group (smallGroup 8 1) := inferInstanceAs (Group (PCGroup smallGroup_8_1))
instance : Group (smallGroup 8 2) := inferInstanceAs (Group (PCGroup smallGroup_8_2))
instance : Group (smallGroup 8 3) := inferInstanceAs (Group (PCGroup smallGroup_8_3))
instance : Group (smallGroup 8 4) := inferInstanceAs (Group (PCGroup smallGroup_8_4))
instance : Group (smallGroup 8 5) := inferInstanceAs (Group (PCGroup smallGroup_8_5))
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

end Smallgroups.GAP
