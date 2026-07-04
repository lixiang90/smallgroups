/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order60.A5
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Smallgroups.UsefulTheorems.SemidirectProductClassify
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Smallgroups.UsefulTheorems.Order4P_12

/-!
# Groups of order 60 with a normal Sylow-5 subgroup

By `card_sylow_5_of_card_60`, a group `G` of order `60` has `1` or `6` Sylow `5`-subgroups. The
`n₅ = 6` case is handled in `Order60.A5` (simplicity, isomorphism to `A₅`). This file handles the
complementary case `n₅ = 1`.

## Main results

* `sixty_semidirectProduct`: if `n₅ = 1` then `G ≅ N ⋊[φ] K` for `N` the (normal) Sylow-`5`
  subgroup and `K` a complement of order `12` (Schur–Zassenhaus).
* Since `Aut(N) ≅ (ZMod 5)ˣ` is *abelian*, conjugating the action `φ` by an automorphism of `N`
  does nothing (`Inn` is trivial on an abelian group), so two actions `φ, φ' : K →* Aut N` give
  isomorphic semidirect products **iff they lie in the same `Aut K`-orbit** (no separate
  `Aut(Aut N)`-move is available, unlike for a general characteristic-subgroup classification).
* Concrete representatives, one for each of the five isomorphism types of order-`12` group `K`
  (`ℤ/12`, `ℤ/2 × ℤ/6`, `Dic₃`, `ℤ/2 × D₆`, `A₄`) and each of the actions realised by that `K`:
  - the **trivial** action, giving the direct product `ℤ/5 × K`, for every `K` (`5` classes);
  - for `K = ℤ/12` and `K = Dic₃` (both of which have abelianization `ℤ/4`), the **order-2**
    action (factoring through the unique index-`2` subgroup) and the **faithful** order-`4`
    action (`4` further classes);
  - for `K = ℤ/2 × ℤ/6` (whose three index-`2` subgroups are permuted transitively by `Aut K`),
    a single **order-2** action, through the `ℤ/2` factor (`1` further class);
  - for `K = ℤ/2 × D₆` (whose index-`2` subgroups fall into **two** `Aut K`-orbits: the two
    `D₆`-copies, and the cyclic `ℤ/6`), the order-2 action through the `ℤ/2` direct factor
    (giving `D₁₀ × D₆`) *and* the order-2 action through the sign of the dihedral component
    (giving `D₆₀ ≅ ℤ/2 × D₃₀`) — `2` further classes.

  `A₄` (abelianization `ℤ/3`, coprime to `4`) admits no nontrivial action. This exhibits the
  `12` representatives of the solvable classes, matching the literature count (`13` groups of
  order `60`, of which `A₅` is the unique non-solvable one). Distinctness and the full
  `IsClassif 60` bundle are left as further work.
-/

namespace Smallgroups.UsefulTheorems

open Sylow Subgroup

variable {G : Type*} [Group G]

/-! ### Reduction: `n₅ = 1` gives a semidirect product `N ⋊[φ] K`, `|N| = 5`, `|K| = 12` -/

private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- When `n₅ = 1`, the Sylow-`5` subgroup is normal. -/
theorem sylow5_normal_of_card_sylow5_eq_one [Finite G] (h1 : Nat.card (Sylow 5 G) = 1)
    (P : Sylow 5 G) : (↑P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
  exact Sylow.normal_of_subsingleton P

/-- The Sylow-`5` subgroup of a group of order `60` has order `5`. -/
theorem card_sylow5_subgroup_of_card_sixty [Finite G] (hG : Nat.card G = 60) (P : Sylow 5 G) :
    Nat.card (↑P : Subgroup G) = 5 := by
  have hndvd : ¬ (5 : ℕ) ∣ 12 := by norm_num
  have hfact : (60 : ℕ).factorization 5 = 1 := by
    rw [show (60 : ℕ) = 12 * 5 from by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hndvd,
      (by norm_num : Nat.Prime 5).factorization_self, zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]

/-- **Schur–Zassenhaus reduction for order `60` with `n₅ = 1`.** The group splits as `N ⋊[φ] K`
where `N` is the normal Sylow-`5` subgroup (order `5`) and `K` has order `12`. -/
theorem sixty_semidirectProduct [Finite G] (hG : Nat.card G = 60)
    (h1 : Nat.card (Sylow 5 G) = 1) :
    ∃ (N K : Subgroup G) (φ : K →* MulAut N),
      N.Normal ∧ Nat.card N = 5 ∧ Nat.card K = 12 ∧
        Nonempty (G ≃* SemidirectProduct N K φ) := by
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 5 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := sylow5_normal_of_card_sylow5_eq_one h1 P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 5 := card_sylow5_subgroup_of_card_sixty hG P0
  obtain ⟨K, φ, ⟨e⟩⟩ := schurZassenhaus_of_card (m := 5) (n := 12) hG (by norm_num)
    (↑P0 : Subgroup G) hcardN
  have hcardK : Nat.card K = 12 := by
    have h1' : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card K := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1'
    omega
  exact ⟨↑P0, K, φ, hnorm, hcardN, hcardK, ⟨e⟩⟩

/-! ### The abstract representative `N = ℤ/5` and its (abelian) automorphism group -/

/-- The order-`4` unit `2` (a primitive root mod `5`), giving the **faithful** action. -/
def cFaithful : (ZMod 5)ˣ := ZMod.unitOfCoprime 2 (by decide)

/-- The order-`2` unit `4 = -1` (mod `5`), giving **inversion**. -/
def cInv : (ZMod 5)ˣ := ZMod.unitOfCoprime 4 (by decide)

theorem cFaithful_pow_four : cFaithful ^ 4 = 1 := by decide

theorem cFaithful_pow_two_ne_one : cFaithful ^ 2 ≠ 1 := by decide

theorem cInv_pow_two : cInv ^ 2 = 1 := by decide

theorem cInv_ne_one : cInv ≠ 1 := by decide

/-! ### Trivial actions: `ℤ/5 × K`, one representative per order-`12` type -/

/-- `ℤ/5 × ℤ/12 ≅ ℤ/60` (trivial action on the cyclic `K = ℤ/12`). -/
abbrev sixtyRep_I : Type := Multiplicative (ZMod 5) × fourP_I 3

/-- `ℤ/5 × (ℤ/2 × ℤ/6) ≅ ℤ/2 × ℤ/30` (trivial action on `K = ℤ/2 × ℤ/6`). -/
abbrev sixtyRep_II : Type := Multiplicative (ZMod 5) × fourP_II 3

/-- `ℤ/5 × Dic₃` (trivial action on `K = Dic₃`). -/
abbrev sixtyRep_III : Type := Multiplicative (ZMod 5) × fourP_III 3

/-- `ℤ/5 × (ℤ/2 × D₆)` (trivial action on `K = ℤ/2 × D₆`). -/
abbrev sixtyRep_V : Type := Multiplicative (ZMod 5) × fourP_V 3

/-- `ℤ/5 × A₄` (the only action `A₄` admits, since `Aut(A₄) → Aut(ℤ/5)` factors through
`A₄`'s abelianization `ℤ/3`, coprime to `4`). -/
abbrev sixtyRep_A4 : Type := Multiplicative (ZMod 5) × fourP_A4

private theorem card_mult_zmod_five : Nat.card (Multiplicative (ZMod 5)) = 5 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem card_sixtyRep_I : Nat.card sixtyRep_I = 60 := by
  rw [sixtyRep_I, Nat.card_prod, card_mult_zmod_five, card_fourP_I]

theorem card_sixtyRep_II : Nat.card sixtyRep_II = 60 := by
  rw [sixtyRep_II, Nat.card_prod, card_mult_zmod_five, card_fourP_II]

theorem card_sixtyRep_III : Nat.card sixtyRep_III = 60 := by
  rw [sixtyRep_III, Nat.card_prod, card_mult_zmod_five, card_fourP_III 3 (by norm_num)]

theorem card_sixtyRep_V : Nat.card sixtyRep_V = 60 := by
  rw [sixtyRep_V, Nat.card_prod, card_mult_zmod_five, card_fourP_V]

theorem card_sixtyRep_A4 : Nat.card sixtyRep_A4 = 60 := by
  rw [sixtyRep_A4, Nat.card_prod, card_mult_zmod_five, card_fourP_A4]

/-! ### Nontrivial actions on the cyclic `K = ℤ/12` -/

theorem cInv_pow_twelve : cInv ^ (12 : ℕ) = 1 := by
  rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, cInv_pow_two, one_pow]

theorem cFaithful_pow_twelve : cFaithful ^ (12 : ℕ) = 1 := by
  rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, cFaithful_pow_four, one_pow]

/-- `ℤ/5 ⋊ ℤ/12` with the order-`2` (non-faithful) action `x ↦ -x`. -/
abbrev sixtyRep_I_inv : Type := NonabRep cInv cInv_pow_twelve

/-- `ℤ/5 ⋊ ℤ/12` with the faithful order-`4` action `x ↦ 2x`. -/
abbrev sixtyRep_I_faithful : Type := NonabRep cFaithful cFaithful_pow_twelve

theorem card_sixtyRep_I_inv : Nat.card sixtyRep_I_inv = 60 := card_nonabRep cInv cInv_pow_twelve

theorem card_sixtyRep_I_faithful : Nat.card sixtyRep_I_faithful = 60 :=
  card_nonabRep cFaithful cFaithful_pow_twelve

/-! ### Nontrivial actions on `K = Dic₃` (abelianization `ℤ/4`, via the `ℤ/4` factor) -/

theorem cInv_pow_four : cInv ^ (4 : ℕ) = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, cInv_pow_two, one_pow]

/-- The action of `Dic₃ = ℤ/3 ⋊[-1] ℤ/4` on `ℤ/5`: trivial on the normal `ℤ/3`, and on the `ℤ/4`
factor by the unit `c` (with `c⁴ = 1`), via `SemidirectProduct.lift`. Since the target `(ZMod 5)ˣ`
is abelian, the compatibility condition is automatic. -/
noncomputable def dic3ActionHom (c : (ZMod 5)ˣ) (hc : c ^ (4 : ℕ) = 1) :
    fourP_III 3 →* MulAut (Multiplicative (ZMod 5)) :=
  unitAutHom.comp <|
    SemidirectProduct.lift (1 : Multiplicative (ZMod 3) →* (ZMod 5)ˣ) (powHom c hc)
      (fun h => by ext n; simp)

/-- `ℤ/5 ⋊ Dic₃` with the order-`2` action (through `Dic₃`'s `ℤ/4`-quotient inverting). -/
abbrev sixtyRep_III_inv : Type :=
  SemidirectProduct (Multiplicative (ZMod 5)) (fourP_III 3) (dic3ActionHom cInv cInv_pow_four)

/-- `ℤ/5 ⋊ Dic₃` with the faithful order-`4` action. -/
abbrev sixtyRep_III_faithful : Type :=
  SemidirectProduct (Multiplicative (ZMod 5)) (fourP_III 3)
    (dic3ActionHom cFaithful cFaithful_pow_four)

theorem card_sixtyRep_III_inv : Nat.card sixtyRep_III_inv = 60 := by
  rw [sixtyRep_III_inv, SemidirectProduct.card, card_mult_zmod_five, card_fourP_III 3 (by norm_num)]

theorem card_sixtyRep_III_faithful : Nat.card sixtyRep_III_faithful = 60 := by
  rw [sixtyRep_III_faithful, SemidirectProduct.card, card_mult_zmod_five,
    card_fourP_III 3 (by norm_num)]

/-! ### A nontrivial action on `K = ℤ/2 × ℤ/6` (through the `ℤ/2` factor) -/

/-- The action of `ℤ/2 × ℤ/6` on `ℤ/5` through the `ℤ/2` factor by the unit `c` (`c² = 1`),
ignoring the `ℤ/6` factor. -/
noncomputable def prodZMod2ActionHom {H : Type*} [Group H] (c : (ZMod 5)ˣ) (hc : c ^ (2 : ℕ) = 1) :
    Multiplicative (ZMod 2) × H →* MulAut (Multiplicative (ZMod 5)) :=
  (unitAutHom.comp (powHom c hc)).comp (MonoidHom.fst (Multiplicative (ZMod 2)) H)

/-- `ℤ/5 ⋊ (ℤ/2 × ℤ/6)` with the order-`2` action through the `ℤ/2` factor. -/
abbrev sixtyRep_II_inv : Type :=
  SemidirectProduct (Multiplicative (ZMod 5)) (fourP_II 3)
    (prodZMod2ActionHom (H := Multiplicative (ZMod 6)) cInv cInv_pow_two)

theorem card_sixtyRep_II_inv : Nat.card sixtyRep_II_inv = 60 := by
  rw [sixtyRep_II_inv, SemidirectProduct.card, card_mult_zmod_five, card_fourP_II]

/-! ### Nontrivial actions on `K = ℤ/2 × D₆`

`K = ℤ/2 × D₆` has abelianization `ℤ/2 × ℤ/2`, so `Hom(K, Aut(ℤ/5))` has four elements: the
trivial one and three of order `2`, with kernels the three index-`2` subgroups of `K`. Under
`Aut(K)` the two subgroups isomorphic to `D₆` (namely `{1} × D₆` and its "diagonal" twin) are
interchanged, but the cyclic one (`ℤ/2 × ⟨r⟩ ≅ ℤ/6`) is preserved — so there are **two**
distinct nontrivial classes:

* action through the `ℤ/2` direct factor (kernel `≅ D₆`), giving `D₁₀ × D₆`;
* action through the *sign* of the dihedral component — reflections invert `ℤ/5`, rotations fix
  it — (kernel `≅ ℤ/6`), giving the dihedral group `D₆₀ ≅ ℤ/2 × D₃₀`.
-/

/-- `ℤ/5 ⋊ (ℤ/2 × D₆)` with the order-`2` action through the `ℤ/2` factor: `D₁₀ × D₆`. -/
abbrev sixtyRep_V_inv : Type :=
  SemidirectProduct (Multiplicative (ZMod 5)) (fourP_V 3)
    (prodZMod2ActionHom (H := DihedralGroup 3) cInv cInv_pow_two)

theorem card_sixtyRep_V_inv : Nat.card sixtyRep_V_inv = 60 := by
  rw [sixtyRep_V_inv, SemidirectProduct.card, card_mult_zmod_five, card_fourP_V]

/-- The sign character `D₆ →* (ZMod 5)ˣ`: rotations act trivially, reflections by `-1`. -/
def d6SignUnitHom : DihedralGroup 3 →* (ZMod 5)ˣ where
  toFun
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => cInv
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · rfl
    · simp [DihedralGroup.r_mul_sr]
    · simp [DihedralGroup.sr_mul_r]
    · simp only [DihedralGroup.sr_mul_sr]
      decide

/-- The sign action of `ℤ/2 × D₆` on `ℤ/5`: the `ℤ/2` factor and the rotations act trivially,
the reflections invert. -/
noncomputable def prodD6SignActionHom :
    fourP_V 3 →* MulAut (Multiplicative (ZMod 5)) :=
  (unitAutHom.comp d6SignUnitHom).comp
    (MonoidHom.snd (Multiplicative (ZMod 2)) (DihedralGroup 3))

/-- `ℤ/5 ⋊ (ℤ/2 × D₆)` with the sign action (reflections invert `ℤ/5`): the dihedral group
`D₆₀ ≅ ℤ/2 × D₃₀`, the twelfth solvable class of order `60`. -/
abbrev sixtyRep_V_sign : Type :=
  SemidirectProduct (Multiplicative (ZMod 5)) (fourP_V 3) prodD6SignActionHom

theorem card_sixtyRep_V_sign : Nat.card sixtyRep_V_sign = 60 := by
  rw [sixtyRep_V_sign, SemidirectProduct.card, card_mult_zmod_five, card_fourP_V]

end Smallgroups.UsefulTheorems
