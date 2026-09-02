/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.ParentTableAlignment
import Smallgroups.GAP.Polycyclic.Imported.Order16Match

/-! Alignment from each Wild order-16 representative to its certified table. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def wildParentGapIndex : Fin 14 → Fin 14
  | 0 => 13
  | 1 => 4
  | 2 => 7
  | 3 => 5
  | 4 => 6
  | 5 => 8
  | 6 => 0
  | 7 => 9
  | 8 => 10
  | 9 => 2
  | 10 => 12
  | 11 => 11
  | 12 => 3
  | 13 => 1

noncomputable def wildParentTableEquiv : ∀ i : Fin 14,
    CertifiedTableGroup (order16ParentTable (wildParentGapIndex i)) ≃*
      order16_wild_reps i
  | 0 => parent14TableGapEquiv.trans order16_14_equiv
  | 1 => parent5TableGapEquiv.trans order16_5_equiv
  | 2 => parent8TableGapEquiv.trans order16_8_equiv
  | 3 => parent6TableGapEquiv.trans order16_6_equiv
  | 4 => parent7TableGapEquiv.trans order16_7_equiv
  | 5 => parent9TableGapEquiv.trans order16_9_equiv
  | 6 => parent1TableGapEquiv.trans order16_1_equiv
  | 7 => parent10TableGapEquiv.trans order16_10_equiv
  | 8 => parent11TableGapEquiv.trans order16_11_equiv
  | 9 => parent3TableGapEquiv.trans order16_3_equiv
  | 10 => parent13TableGapEquiv.trans order16_13_equiv
  | 11 => parent12TableGapEquiv.trans order16_12_equiv
  | 12 => parent4TableGapEquiv.trans order16_4_equiv
  | 13 => parent2TableGapEquiv.trans order16_2_equiv

end Smallgroups.UsefulTheorems.Order32Certificate
