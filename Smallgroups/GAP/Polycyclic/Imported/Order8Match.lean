/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order8
import Smallgroups.Classifications.Classifications_1_to_10.Order8

/-!
# Verification: order `8` — the imported pc groups match the existing representatives

The five groups of order `8` in the GAP SmallGroups library are

* `SmallGroup(8, 1) = ℤ/8` — `g₁² = g₂`, `g₂² = g₃`, abelian;
* `SmallGroup(8, 2) = ℤ/4 × ℤ/2` — `g₁² = g₃`, abelian;
* `SmallGroup(8, 3) = D₄` — `g₂^{g₁} = g₂ g₃` (dihedral);
* `SmallGroup(8, 4) = Q₈` — `g₁² = g₂² = g₃`, `g₂^{g₁} = g₂ g₃` (quaternion);
* `SmallGroup(8, 5) = (ℤ/2)³` — elementary abelian.

Each is proved isomorphic to the corresponding representative of the project's
existing order-`8` classification (`Classifications_1_to_10/Order8`), by mapping the
pc generators to explicit elements and certifying homomorphism + bijectivity by
`decide` (`mulEquivOfDecide`).
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems P3Group

/-- `SmallGroup(8, 1) = ℤ/8`, mapping `g₁ ↦ 1`, `g₂ ↦ 2`, `g₃ ↦ 4`. -/
noncomputable def order8_1_equiv :
    PCGroup smallGroup_8_1 ≃* Multiplicative (CyclicP3 2) :=
  mulEquivOfDecide
    (pcEval [sg8_1_L1, sg8_1_L2, sg8_1_L3]
      [Multiplicative.ofAdd 1, Multiplicative.ofAdd 2, Multiplicative.ofAdd 4])

/-- `SmallGroup(8, 2) = ℤ/4 × ℤ/2`, mapping `g₁ ↦ (1, 0)`, `g₂ ↦ (0, 1)`,
`g₃ ↦ (2, 0)`. -/
noncomputable def order8_2_equiv :
    PCGroup smallGroup_8_2 ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2) :=
  mulEquivOfDecide
    (pcEval [sg8_2_L1, sg8_2_L2, sg8_2_L3]
      [(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),
        (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),
        (Multiplicative.ofAdd 2, Multiplicative.ofAdd 0)])

/-- `SmallGroup(8, 3) = D₄`, mapping `g₁ ↦ sr 1`, `g₂ ↦ sr 0`, `g₃ ↦ r 2`. -/
noncomputable def order8_3_equiv : PCGroup smallGroup_8_3 ≃* DihedralGroup 4 :=
  mulEquivOfDecide
    (pcEval [sg8_3_L1, sg8_3_L2, sg8_3_L3]
      [DihedralGroup.sr 1, DihedralGroup.sr 0, DihedralGroup.r 2])

/-- `SmallGroup(8, 4) = Q₈`, mapping `g₁ ↦ xa 0`, `g₂ ↦ xa 1`, `g₃ ↦ a 2`. -/
noncomputable def order8_4_equiv : PCGroup smallGroup_8_4 ≃* QuaternionGroup 2 :=
  mulEquivOfDecide
    (pcEval [sg8_4_L1, sg8_4_L2, sg8_4_L3]
      [QuaternionGroup.xa 0, QuaternionGroup.xa 1, QuaternionGroup.a 2])

/-- `SmallGroup(8, 5) = (ℤ/2)³`, mapping `g₁, g₂, g₃` to the standard basis. -/
noncomputable def order8_5_equiv :
    PCGroup smallGroup_8_5 ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  mulEquivOfDecide
    (pcEval [sg8_5_L1, sg8_5_L2, sg8_5_L3]
      [(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0),
        (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),
        (Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)])

end Smallgroups.GAP
