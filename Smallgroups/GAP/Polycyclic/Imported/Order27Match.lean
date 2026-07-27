/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Imported.Order27
import Smallgroups.Classifications.Classifications_21_to_30.Order27

/-!
# Verification: order `27` — the imported pc groups match the existing representatives

The five groups of order `27` in the GAP SmallGroups library are

* `SmallGroup(27, 1) = ℤ/27` — `g₁³ = g₂`, `g₂³ = g₃`, abelian;
* `SmallGroup(27, 2) = ℤ/9 × ℤ/3` — `g₁³ = g₃`, abelian;
* `SmallGroup(27, 3)` — exponent `3`, `g₂^{g₁⁻¹} = g₂ g₃²`: the Heisenberg group;
* `SmallGroup(27, 4)` — `g₁³ = g₃`, `g₂^{g₁⁻¹} = g₂ g₃²`: `ℤ/9 ⋊ ℤ/3`;
* `SmallGroup(27, 5) = (ℤ/3)³` — elementary abelian.

Each is proved isomorphic to the corresponding representative of the project's
existing order-`27` classification (`Classifications_21_to_30/Order27`), by mapping
the pc generators to explicit elements and certifying homomorphism + bijectivity by
`decide` (`mulEquivOfDecide`).
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems P3Group

/-- `SmallGroup(27, 1) = ℤ/27`, mapping `g₁ ↦ 1`, `g₂ ↦ 3`, `g₃ ↦ 9`. -/
noncomputable def order27_1_equiv :
    PCGroup smallGroup_27_1 ≃* Multiplicative (CyclicP3 3) :=
  mulEquivOfDecide
    (pcEval [sg27_1_L1, sg27_1_L2, sg27_1_L3]
      [Multiplicative.ofAdd 1, Multiplicative.ofAdd 3, Multiplicative.ofAdd 9])

/-- `SmallGroup(27, 2) = ℤ/9 × ℤ/3`, mapping `g₁ ↦ (1, 0)`, `g₂ ↦ (0, 1)`,
`g₃ ↦ (3, 0)`. -/
noncomputable def order27_2_equiv :
    PCGroup smallGroup_27_2 ≃* Multiplicative (ZMod 9) × Multiplicative (ZMod 3) :=
  mulEquivOfDecide
    (pcEval [sg27_2_L1, sg27_2_L2, sg27_2_L3]
      [(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),
        (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),
        (Multiplicative.ofAdd 3, Multiplicative.ofAdd 0)])

/-- `SmallGroup(27, 3)` is the Heisenberg group, mapping
`g₁ ↦ (0,1,0)`, `g₂ ↦ (1,0,0)`, `g₃ ↦ (0,0,1)`. -/
noncomputable def order27_3_equiv : PCGroup smallGroup_27_3 ≃* HeisenbergGroup 3 :=
  mulEquivOfDecide
    (pcEval [sg27_3_L1, sg27_3_L2, sg27_3_L3]
      [⟨0, 1, 0⟩, ⟨1, 0, 0⟩, ⟨0, 0, 1⟩])

/-- `SmallGroup(27, 4) = ℤ/9 ⋊ ℤ/3`, mapping `g₁ ↦ (1, 0)`, `g₂ ↦ (0, 1)`,
`g₃ ↦ (3, 0)`. -/
noncomputable def order27_4_equiv : PCGroup smallGroup_27_4 ≃* SemidirectP2P 3 :=
  mulEquivOfDecide
    (pcEval [sg27_4_L1, sg27_4_L2, sg27_4_L3]
      [⟨1, 0⟩, ⟨0, 1⟩, ⟨3, 0⟩])

/-- `SmallGroup(27, 5) = (ℤ/3)³`, mapping `g₁, g₂, g₃` to the standard basis. -/
noncomputable def order27_5_equiv :
    PCGroup smallGroup_27_5 ≃*
      Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3) :=
  mulEquivOfDecide
    (pcEval [sg27_5_L1, sg27_5_L2, sg27_5_L3]
      [(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0),
        (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),
        (Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)])

end Smallgroups.GAP
