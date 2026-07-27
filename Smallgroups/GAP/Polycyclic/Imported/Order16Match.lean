/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order16
import Smallgroups.Classifications.Classifications_11_to_20.Order16

/-!
# Verification: order `16` — the imported pc groups match the existing representatives

The fourteen groups of order `16` in the GAP SmallGroups library are matched with the
project's order-`16` classification representatives (`order16_wild_G0`–`order16_wild_G13`,
Wild numbering) as follows:

* `SmallGroup(16, 1) = ℤ/16` — `G₆` (cyclic);
* `SmallGroup(16, 2) = ℤ/4 × ℤ/4` — `G₁₃`;
* `SmallGroup(16, 3) = K₄ ⋊ ℤ/4` — `G₉` (abelianization `ℤ/4 × ℤ/2`);
* `SmallGroup(16, 4) = ℤ/4 ⋊ ℤ/4` — `G₁₂`;
* `SmallGroup(16, 5) = ℤ/8 × ℤ/2` — `G₁`;
* `SmallGroup(16, 6) = ℤ/8 ⋊₅ ℤ/2` (modular) — `G₃`;
* `SmallGroup(16, 7) = D₁₆` (dihedral) — `G₄`;
* `SmallGroup(16, 8) = SD₁₆` (semidihedral) — `G₂`;
* `SmallGroup(16, 9) = Q₁₆` (generalized quaternion) — `G₅`;
* `SmallGroup(16, 10) = ℤ/4 × ℤ/2 × ℤ/2` — `G₇`;
* `SmallGroup(16, 11) = D₈ × ℤ/2` — `G₈`;
* `SmallGroup(16, 12) = Q₈ × ℤ/2` — `G₁₁`;
* `SmallGroup(16, 13) = Q₈ ⋊ ℤ/2` — `G₁₀` (abelianization `(ℤ/2)³`, contains `Q₈`);
* `SmallGroup(16, 14) = (ℤ/2)⁴` — `G₀`.

(The two `(ℤ/4 × ℤ/2) ⋊ ℤ/2` groups `16.3`/`16.13` are told apart by their abelianizations
and by the presence of a `Q₈` subgroup, checked with GAP.)

Each isomorphism is certified by mapping the pc generators `g₁, g₂, g₃, g₄` (outermost
first) to explicit elements of the representative and discharging homomorphism +
bijectivity by `decide` (`mulEquivOfDecide`).
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

/-- `SmallGroup(16, 1) = ℤ/16` (concrete model), mapping `g₁ ↦ 1`, `g₂ ↦ 2`, `g₃ ↦ 4`,
`g₄ ↦ 8`. -/
noncomputable def order16_1_equiv_concrete :
    PCGroup smallGroup_16_1 ≃* Multiplicative (ZMod 16) :=
  mulEquivOfDecide
    (pcEval [sg16_1_L1, sg16_1_L2, sg16_1_L3, sg16_1_L4]
      [Multiplicative.ofAdd 1, Multiplicative.ofAdd 2,
        Multiplicative.ofAdd 4, Multiplicative.ofAdd 8])

/-- `SmallGroup(16, 1) = ℤ/16 = G₆`. -/
noncomputable def order16_1_equiv : PCGroup smallGroup_16_1 ≃* order16_wild_G6 :=
  order16_1_equiv_concrete.trans order16_A1_iso_concrete.some.symm

/-- `SmallGroup(16, 2) = ℤ/4 × ℤ/4` (concrete model), mapping `g₁ ↦ (0, 1)`,
`g₂ ↦ (1, 0)`, `g₃ ↦ (0, 2)`, `g₄ ↦ (2, 0)`. -/
noncomputable def order16_2_equiv_concrete :
    PCGroup smallGroup_16_2 ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  mulEquivOfDecide
    (pcEval [sg16_2_L1, sg16_2_L2, sg16_2_L3, sg16_2_L4]
      [(1, Multiplicative.ofAdd 1),
        (Multiplicative.ofAdd 1, 1),
        (1, Multiplicative.ofAdd 2),
        (Multiplicative.ofAdd 2, 1)])

/-- `SmallGroup(16, 2) = ℤ/4 × ℤ/4 = G₁₃`. -/
noncomputable def order16_2_equiv : PCGroup smallGroup_16_2 ≃* order16_wild_G13 :=
  order16_2_equiv_concrete.trans order16_A3_iso_concrete.some.symm

/-- `SmallGroup(16, 3) = K₄ ⋊ ℤ/4 = G₉`, mapping `g₁ ↦ x`, `g₂ ↦ t`, `g₃ ↦ y`,
`g₄ ↦ x²` (with `K₈ = ⟨x, y⟩` and `t` the acting involution via `ψ₅`). -/
noncomputable def order16_3_equiv : PCGroup smallGroup_16_3 ≃* order16_wild_G9 :=
  mulEquivOfDecide
    (pcEval [sg16_3_L1, sg16_3_L2, sg16_3_L3, sg16_3_L4]
      [⟨(Multiplicative.ofAdd 1, 1), 1⟩,
        ⟨(1, 1), Multiplicative.ofAdd 1⟩,
        ⟨(1, Multiplicative.ofAdd 1), 1⟩,
        ⟨(Multiplicative.ofAdd 2, 1), 1⟩])

/-- `SmallGroup(16, 4) = ℤ/4 ⋊ ℤ/4 = G₁₂`, mapping `g₁ ↦ t`, `g₂ ↦ x`,
`g₃ ↦ x²`, `g₄ ↦ t²` (with `x` the normal `ℤ/4` and `t` the acting `ℤ/4`). -/
noncomputable def order16_4_equiv : PCGroup smallGroup_16_4 ≃* order16_wild_G12 :=
  mulEquivOfDecide
    (pcEval [sg16_4_L1, sg16_4_L2, sg16_4_L3, sg16_4_L4]
      [⟨1, Multiplicative.ofAdd 1⟩,
        ⟨Multiplicative.ofAdd 1, 1⟩,
        ⟨Multiplicative.ofAdd 2, 1⟩,
        ⟨1, Multiplicative.ofAdd 2⟩])

/-- `SmallGroup(16, 5) = ℤ/8 × ℤ/2 = G₁`, mapping `g₁ ↦ (1, 0)`, `g₂ ↦ (0, 1)`,
`g₃ ↦ (2, 0)`, `g₄ ↦ (4, 0)`. -/
noncomputable def order16_5_equiv : PCGroup smallGroup_16_5 ≃* order16_wild_G1 :=
  mulEquivOfDecide
    (pcEval [sg16_5_L1, sg16_5_L2, sg16_5_L3, sg16_5_L4]
      [(Multiplicative.ofAdd 1, 1),
        (1, Multiplicative.ofAdd 1),
        (Multiplicative.ofAdd 2, 1),
        (Multiplicative.ofAdd 4, 1)])

/-- `SmallGroup(16, 6) = ℤ/8 ⋊₅ ℤ/2 = G₃` (modular), mapping `g₁ ↦ x`, `g₂ ↦ t`,
`g₃ ↦ x²`, `g₄ ↦ x⁴`. -/
noncomputable def order16_6_equiv : PCGroup smallGroup_16_6 ≃* order16_wild_G3 :=
  mulEquivOfDecide
    (pcEval [sg16_6_L1, sg16_6_L2, sg16_6_L3, sg16_6_L4]
      [⟨Multiplicative.ofAdd 1, 1⟩,
        ⟨1, Multiplicative.ofAdd 1⟩,
        ⟨Multiplicative.ofAdd 2, 1⟩,
        ⟨Multiplicative.ofAdd 4, 1⟩])

/-- `SmallGroup(16, 7) = D₁₆ = G₄`, mapping `g₁ ↦ t`, `g₂ ↦ x t`, `g₃ ↦ x²`,
`g₄ ↦ x⁴` (with `x` the rotation and `t` a reflection). -/
noncomputable def order16_7_equiv : PCGroup smallGroup_16_7 ≃* order16_wild_G4 :=
  mulEquivOfDecide
    (pcEval [sg16_7_L1, sg16_7_L2, sg16_7_L3, sg16_7_L4]
      [⟨1, Multiplicative.ofAdd 1⟩,
        ⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 1⟩,
        ⟨Multiplicative.ofAdd 2, 1⟩,
        ⟨Multiplicative.ofAdd 4, 1⟩])

/-- `SmallGroup(16, 8) = SD₁₆ = G₂` (semidihedral), mapping `g₁ ↦ x t`, `g₂ ↦ t`,
`g₃ ↦ x²`, `g₄ ↦ x⁴`. -/
noncomputable def order16_8_equiv : PCGroup smallGroup_16_8 ≃* order16_wild_G2 :=
  mulEquivOfDecide
    (pcEval [sg16_8_L1, sg16_8_L2, sg16_8_L3, sg16_8_L4]
      [⟨Multiplicative.ofAdd 1, Multiplicative.ofAdd 1⟩,
        ⟨1, Multiplicative.ofAdd 1⟩,
        ⟨Multiplicative.ofAdd 2, 1⟩,
        ⟨Multiplicative.ofAdd 4, 1⟩])

/-- `SmallGroup(16, 9) = Q₁₆ = G₅`, mapping `g₁ ↦ xa 0`, `g₂ ↦ xa 1`, `g₃ ↦ a 6`,
`g₄ ↦ a 4`. -/
noncomputable def order16_9_equiv : PCGroup smallGroup_16_9 ≃* order16_wild_G5 :=
  mulEquivOfDecide
    (pcEval [sg16_9_L1, sg16_9_L2, sg16_9_L3, sg16_9_L4]
      [QuaternionGroup.xa 0, QuaternionGroup.xa 1,
        QuaternionGroup.a 6, QuaternionGroup.a 4])

/-- `SmallGroup(16, 10) = ℤ/4 × ℤ/2 × ℤ/2 = G₇`, mapping `g₁ ↦ ((1, 0), 0)`,
`g₂ ↦ ((0, 0), 1)`, `g₃ ↦ ((0, 1), 0)`, `g₄ ↦ ((2, 0), 0)`. -/
noncomputable def order16_10_equiv : PCGroup smallGroup_16_10 ≃* order16_wild_G7 :=
  mulEquivOfDecide
    (pcEval [sg16_10_L1, sg16_10_L2, sg16_10_L3, sg16_10_L4]
      [((Multiplicative.ofAdd 1, 1), 1),
        ((1, 1), Multiplicative.ofAdd 1),
        ((1, Multiplicative.ofAdd 1), 1),
        ((Multiplicative.ofAdd 2, 1), 1)])

/-- `SmallGroup(16, 11) = D₈ × ℤ/2 = G₈`, mapping `g₁ ↦ t`, `g₂ ↦ x t`, `g₃ ↦ y`,
`g₄ ↦ x²` (with `K₈ = ⟨x, y⟩`, `t` acting via `ψ₃`). -/
noncomputable def order16_11_equiv : PCGroup smallGroup_16_11 ≃* order16_wild_G8 :=
  mulEquivOfDecide
    (pcEval [sg16_11_L1, sg16_11_L2, sg16_11_L3, sg16_11_L4]
      [⟨(1, 1), Multiplicative.ofAdd 1⟩,
        ⟨(Multiplicative.ofAdd 1, 1), Multiplicative.ofAdd 1⟩,
        ⟨(1, Multiplicative.ofAdd 1), 1⟩,
        ⟨(Multiplicative.ofAdd 2, 1), 1⟩])

/-- `SmallGroup(16, 12) = Q₈ × ℤ/2 = G₁₁`, mapping `g₁ ↦ (a 1, 0)`,
`g₂ ↦ (xa 0, 0)`, `g₃ ↦ (1, 1)`, `g₄ ↦ (a 2, 0)`. -/
noncomputable def order16_12_equiv : PCGroup smallGroup_16_12 ≃* order16_wild_G11 :=
  mulEquivOfDecide
    (pcEval [sg16_12_L1, sg16_12_L2, sg16_12_L3, sg16_12_L4]
      [(QuaternionGroup.a 1, 1),
        (QuaternionGroup.xa 0, 1),
        (1, Multiplicative.ofAdd 1),
        (QuaternionGroup.a 2, 1)])

/-- `SmallGroup(16, 13) = Q₈ ⋊ ℤ/2 = G₁₀`, mapping `g₁ ↦ t`, `g₂ ↦ y`,
`g₃ ↦ x y`, `g₄ ↦ x²` (with `K₈ = ⟨x, y⟩`, `t` acting via `ψ₆`). -/
noncomputable def order16_13_equiv : PCGroup smallGroup_16_13 ≃* order16_wild_G10 :=
  mulEquivOfDecide
    (pcEval [sg16_13_L1, sg16_13_L2, sg16_13_L3, sg16_13_L4]
      [⟨(1, 1), Multiplicative.ofAdd 1⟩,
        ⟨(1, Multiplicative.ofAdd 1), 1⟩,
        ⟨(Multiplicative.ofAdd 1, Multiplicative.ofAdd 1), 1⟩,
        ⟨(Multiplicative.ofAdd 2, 1), 1⟩])

/-- `SmallGroup(16, 14) = (ℤ/2)⁴` (concrete model), mapping `g₁, g₂, g₃, g₄` to the
standard basis. -/
noncomputable def order16_14_equiv_concrete :
    PCGroup smallGroup_16_14 ≃* order16_wild_C2pow4 :=
  mulEquivOfDecide
    (pcEval [sg16_14_L1, sg16_14_L2, sg16_14_L3, sg16_14_L4]
      [(Multiplicative.ofAdd 1, 1, 1, 1),
        (1, Multiplicative.ofAdd 1, 1, 1),
        (1, 1, Multiplicative.ofAdd 1, 1),
        (1, 1, 1, Multiplicative.ofAdd 1)])

/-- `SmallGroup(16, 14) = (ℤ/2)⁴ = G₀`. -/
noncomputable def order16_14_equiv : PCGroup smallGroup_16_14 ≃* order16_wild_G0 :=
  order16_14_equiv_concrete.trans order16_A5_iso_concrete.some.symm

end Smallgroups.GAP
