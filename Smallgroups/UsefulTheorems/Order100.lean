/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Smallgroups.UsefulTheorems.SemidirectProductClassify
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum.Prime

/-!
# First reductions for groups of order 100

Since `100 = 4 * 5²`, the Sylow `5`-subgroup is normal.  Thus every group of
order `100` splits as `P ⋊ H`, where `P` has order `25` and `H` has order `4`.

This file records that reduction and standardises the two factors:

* `P` is either `C₂₅` or `(C₅)²`;
* `H` is either `C₄` or `C₂ × C₂`.

The remaining classification work is the orbit calculation for homomorphisms
from the two order-`4` groups to the automorphism groups of the two order-`25`
groups.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-! ### Sylow-5 normality and semidirect-product reduction -/

/-- The Sylow `5`-subgroup is unique in a group of order `100`. -/
theorem card_sylow_5_eq_one_of_card_100 [Finite G] (hG : Nat.card G = 100) :
    Nat.card (Sylow 5 G) = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 5 G))
  have hndvd_5 : ¬ 5 ∣ Nat.card (Sylow 5 G) := not_dvd_card_sylow 5 G
  have hdvd100 : Nat.card (Sylow 5 G) ∣ 100 := by
    rw [← hG]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have h100 : 100 = 4 * 5 ^ 2 := by norm_num
  have hdvd4_mul : Nat.card (Sylow 5 G) ∣ 4 * 5 ^ 2 := by
    simpa [h100] using hdvd100
  have hp5 : Nat.Prime 5 := by norm_num
  have hcop : Nat.Coprime (Nat.card (Sylow 5 G)) (5 ^ 2) :=
    ((hp5.coprime_iff_not_dvd.mpr hndvd_5).symm).pow_right 2
  have hdvd4 : Nat.card (Sylow 5 G) ∣ 4 := hcop.dvd_of_dvd_mul_right hdvd4_mul
  have hmod := card_sylow_modEq_one 5 G
  have hle : Nat.card (Sylow 5 G) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
  have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
  have hlt : Nat.card (Sylow 5 G) < 5 := by omega
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 1 < 5)] at hmod
  exact hmod

/-- The Sylow `5`-subgroup of a group of order `100` is normal. -/
theorem sylow_5_normal_of_card_100 [Finite G] (hG : Nat.card G = 100) (P : Sylow 5 G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Subsingleton (Sylow 5 G) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow_5_eq_one_of_card_100 hG)).1
  exact normal_of_subsingleton P

/-- The Sylow `5`-subgroup of a group of order `100` has order `25`. -/
theorem card_sylow_5_subgroup_of_card_100 [Finite G] (hG : Nat.card G = 100)
    (P : Sylow 5 G) : Nat.card (↑P : Subgroup G) = 25 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hndvd : ¬ 5 ∣ 4 := by norm_num
  have hfact : (100 : ℕ).factorization 5 = 2 := by
    rw [show 100 = 4 * 5 ^ 2 by norm_num,
      Nat.factorization_mul (by norm_num) (pow_ne_zero 2 (by norm_num : (5 : ℕ) ≠ 0)),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hndvd,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 5), zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact]
  norm_num

/-- **Schur-Zassenhaus reduction for order `100`.**
Every group of order `100` is a semidirect product `P ⋊[φ] H`, where
`P` has order `25` and `H` has order `4`. -/
theorem order100_semidirectProduct [Finite G] (hG : Nat.card G = 100) :
    ∃ (P H : Subgroup G) (φ : H →* MulAut P),
      P.Normal ∧ Nat.card P = 25 ∧ Nat.card H = 4 ∧
        Nonempty (G ≃* SemidirectProduct P H φ) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 5 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := sylow_5_normal_of_card_100 hG P0
  have hcardP : Nat.card (↑P0 : Subgroup G) = 25 :=
    card_sylow_5_subgroup_of_card_100 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardP, show 25 = 5 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr
      P0.not_dvd_index)
  obtain ⟨H, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardH : Nat.card H = 4 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardP] at h1
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 25) h1).symm
  exact ⟨↑P0, H, φ, hnorm, hcardP, hcardH, ⟨e⟩⟩

/-! ### Standard factor choices -/

abbrev order100_C25 : Type := CyclicRep 25

abbrev order100_E25 : Type := ElemAbelianRep 5

abbrev order100_C4 : Type := CyclicRep 4

abbrev order100_V4 : Type := ElemAbelianRep 2

abbrev order100_E25_e1 : order100_E25 := (Multiplicative.ofAdd (1 : ZMod 5), 1)

abbrev order100_E25_e2 : order100_E25 := (1, Multiplicative.ofAdd (1 : ZMod 5))

private lemma order100_ofAdd_pow_nat (c : ZMod 5) (n : ℕ) :
    (Multiplicative.ofAdd c : Multiplicative (ZMod 5)) ^ n =
      Multiplicative.ofAdd (↑n * c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← ofAdd_add, Nat.cast_succ, add_mul, one_mul]

private lemma order100_ofAdd_one_pow (n : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod 5)) ^ n =
      Multiplicative.ofAdd (↑n : ZMod 5) := by
  rw [order100_ofAdd_pow_nat, mul_one]

theorem order100_E25_fst_pow (s : Multiplicative (ZMod 5)) :
    ((s, 1) : order100_E25) = order100_E25_e1 ^ (Multiplicative.toAdd s).val := by
  ext
  · simp only [order100_E25_e1, Prod.pow_fst, order100_ofAdd_one_pow,
      ZMod.natCast_zmod_val, ofAdd_toAdd]
  · simp only [order100_E25_e1, Prod.pow_snd, one_pow]

theorem order100_E25_snd_pow (s : Multiplicative (ZMod 5)) :
    ((1, s) : order100_E25) = order100_E25_e2 ^ (Multiplicative.toAdd s).val := by
  ext
  · simp only [order100_E25_e2, Prod.pow_fst, one_pow]
  · simp only [order100_E25_e2, Prod.pow_snd, order100_ofAdd_one_pow,
      ZMod.natCast_zmod_val, ofAdd_toAdd]

theorem order100_E25_vec_decomp (x y : ZMod 5) :
    ((Multiplicative.ofAdd x, Multiplicative.ofAdd y) : order100_E25) =
      order100_E25_e1 ^ x.val * order100_E25_e2 ^ y.val := by
  rw [show ((Multiplicative.ofAdd x, Multiplicative.ofAdd y) : order100_E25) =
      ((Multiplicative.ofAdd x, 1) : order100_E25) * (1, Multiplicative.ofAdd y) by
    ext <;> simp]
  rw [order100_E25_fst_pow, order100_E25_snd_pow]
  simp [toAdd_ofAdd]

theorem order100_E25_vec_ne_one {x y : ZMod 5} (hxy : (x, y) ≠ (0, 0)) :
    ((Multiplicative.ofAdd x, Multiplicative.ofAdd y) : order100_E25) ≠ 1 := by
  intro h
  apply hxy
  apply Prod.ext
  · have h1 := congrArg (fun z : order100_E25 => z.1.toAdd) h
    simpa using h1
  · have h2 := congrArg (fun z : order100_E25 => z.2.toAdd) h
    simpa using h2

theorem order100_E25_hom_ext {M : Type*} [Monoid M] {f g : order100_E25 →* M}
    (h1 : f order100_E25_e1 = g order100_E25_e1)
    (h2 : f order100_E25_e2 = g order100_E25_e2) : f = g := by
  ext ⟨x1, x2⟩
  have hdecomp : ((x1, x2) : order100_E25) = (x1, 1) * (1, x2) := by ext <;> simp
  rw [hdecomp, map_mul, map_mul]
  congr 1
  · rw [order100_E25_fst_pow, map_pow, map_pow, h1]
  · rw [order100_E25_snd_pow, map_pow, map_pow, h2]

theorem order100_E25_mulAut_ext {α β : MulAut order100_E25}
    (h1 : α order100_E25_e1 = β order100_E25_e1)
    (h2 : α order100_E25_e2 = β order100_E25_e2) : α = β := by
  apply MulEquiv.ext
  intro x
  exact congrFun (congrArg DFunLike.coe
    (order100_E25_hom_ext (f := α.toMonoidHom) (g := β.toMonoidHom) h1 h2)) x

instance order100_E25_mulAut_decidableEq : DecidableEq (MulAut order100_E25) := fun α β =>
  decidable_of_iff (∀ x, α x = β x)
    ⟨fun h => MulEquiv.ext h, fun h x => by rw [h]⟩

noncomputable def order100_E25_matrixAut (a b c d : ZMod 5) (hdet : a * d - b * c ≠ 0) :
    MulAut order100_E25 where
  toFun x :=
    (Multiplicative.ofAdd (a * x.1.toAdd + b * x.2.toAdd),
      Multiplicative.ofAdd (c * x.1.toAdd + d * x.2.toAdd))
  invFun x :=
    let Δ := a * d - b * c
    (Multiplicative.ofAdd (Δ⁻¹ * (d * x.1.toAdd - b * x.2.toAdd)),
      Multiplicative.ofAdd (Δ⁻¹ * (-c * x.1.toAdd + a * x.2.toAdd)))
  left_inv x := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    dsimp
    ext <;> simp only [toAdd_ofAdd]
    · calc
        (a * d - b * c)⁻¹ * (d * (a * Multiplicative.toAdd x.1 + b * Multiplicative.toAdd x.2) -
            b * (c * Multiplicative.toAdd x.1 + d * Multiplicative.toAdd x.2))
            = ((a * d - b * c)⁻¹ * (a * d - b * c)) * Multiplicative.toAdd x.1 := by ring
        _ = Multiplicative.toAdd x.1 := by
          rw [show (a * d - b * c)⁻¹ * (a * d - b * c) = 1 by
            exact inv_mul_cancel₀ (a := a * d - b * c) (by simpa using hdet)]
          ring
    · calc
        (a * d - b * c)⁻¹ * (-c * (a * Multiplicative.toAdd x.1 + b * Multiplicative.toAdd x.2) +
            a * (c * Multiplicative.toAdd x.1 + d * Multiplicative.toAdd x.2))
            = ((a * d - b * c)⁻¹ * (a * d - b * c)) * Multiplicative.toAdd x.2 := by ring
        _ = Multiplicative.toAdd x.2 := by
          rw [show (a * d - b * c)⁻¹ * (a * d - b * c) = 1 by
            exact inv_mul_cancel₀ (a := a * d - b * c) (by simpa using hdet)]
          ring
  right_inv x := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    dsimp
    ext
    · calc
        a * ((a * d - b * c)⁻¹ * (d * Multiplicative.toAdd x.1 - b * Multiplicative.toAdd x.2)) +
            b * ((a * d - b * c)⁻¹ * (-c * Multiplicative.toAdd x.1 + a * Multiplicative.toAdd x.2))
            = ((a * d - b * c) * (a * d - b * c)⁻¹) * Multiplicative.toAdd x.1 := by ring
        _ = Multiplicative.toAdd x.1 := by
          rw [show (a * d - b * c) * (a * d - b * c)⁻¹ = 1 by
            exact mul_inv_cancel₀ (a := a * d - b * c) (by simpa using hdet)]
          ring
    · calc
        c * ((a * d - b * c)⁻¹ * (d * Multiplicative.toAdd x.1 - b * Multiplicative.toAdd x.2)) +
            d * ((a * d - b * c)⁻¹ * (-c * Multiplicative.toAdd x.1 + a * Multiplicative.toAdd x.2))
            = ((a * d - b * c) * (a * d - b * c)⁻¹) * Multiplicative.toAdd x.2 := by ring
        _ = Multiplicative.toAdd x.2 := by
          rw [show (a * d - b * c) * (a * d - b * c)⁻¹ = 1 by
            exact mul_inv_cancel₀ (a := a * d - b * c) (by simpa using hdet)]
          ring
  map_mul' x y := by
    ext <;> simp [toAdd_mul, ofAdd_add, mul_add, add_assoc, add_left_comm]

@[simp]
theorem order100_E25_matrixAut_e1 (a b c d : ZMod 5) (hdet : a * d - b * c ≠ 0) :
    order100_E25_matrixAut a b c d hdet order100_E25_e1 =
      (Multiplicative.ofAdd a, Multiplicative.ofAdd c) := by
  ext <;> simp [order100_E25_matrixAut, order100_E25_e1]

@[simp]
theorem order100_E25_matrixAut_e2 (a b c d : ZMod 5) (hdet : a * d - b * c ≠ 0) :
    order100_E25_matrixAut a b c d hdet order100_E25_e2 =
      (Multiplicative.ofAdd b, Multiplicative.ofAdd d) := by
  ext <;> simp [order100_E25_matrixAut, order100_E25_e2]

theorem order100_singular_matrix_has_nonzero_kernel
    (a b c d : ZMod 5) (hdet : a * d - b * c = 0) :
    ∃ x y : ZMod 5, (x, y) ≠ (0, 0) ∧
      a * x + b * y = 0 ∧ c * x + d * y = 0 := by
  decide +revert

theorem order100_E25_mulAut_det_ne_zero (α : MulAut order100_E25) :
    (α order100_E25_e1).1.toAdd * (α order100_E25_e2).2.toAdd -
      (α order100_E25_e2).1.toAdd * (α order100_E25_e1).2.toAdd ≠ 0 := by
  intro hdet
  let a := (α order100_E25_e1).1.toAdd
  let b := (α order100_E25_e2).1.toAdd
  let c := (α order100_E25_e1).2.toAdd
  let d := (α order100_E25_e2).2.toAdd
  have hdet' : a * d - b * c = 0 := by simpa [a, b, c, d] using hdet
  obtain ⟨x, y, hxy, hx, hy⟩ := order100_singular_matrix_has_nonzero_kernel a b c d hdet'
  let z : order100_E25 := (Multiplicative.ofAdd x, Multiplicative.ofAdd y)
  have hz_ne : z ≠ 1 := order100_E25_vec_ne_one hxy
  have he1 : α order100_E25_e1 = (Multiplicative.ofAdd a, Multiplicative.ofAdd c) := by
    ext <;> simp [a, c]
  have he2 : α order100_E25_e2 = (Multiplicative.ofAdd b, Multiplicative.ofAdd d) := by
    ext <;> simp [b, d]
  have hz_decomp : z = order100_E25_e1 ^ x.val * order100_E25_e2 ^ y.val :=
    order100_E25_vec_decomp x y
  have hαz : α z = 1 := by
    rw [hz_decomp, map_mul, map_pow, map_pow, he1, he2]
    apply Prod.ext
    · change (Multiplicative.ofAdd a) ^ x.val * (Multiplicative.ofAdd b) ^ y.val = 1
      rw [order100_ofAdd_pow_nat, order100_ofAdd_pow_nat, ← ofAdd_add]
      change Multiplicative.ofAdd (↑x.val * a + ↑y.val * b) = Multiplicative.ofAdd 0
      apply congrArg Multiplicative.ofAdd
      simpa [ZMod.natCast_zmod_val, add_comm, mul_comm] using hx
    · change (Multiplicative.ofAdd c) ^ x.val * (Multiplicative.ofAdd d) ^ y.val = 1
      rw [order100_ofAdd_pow_nat, order100_ofAdd_pow_nat, ← ofAdd_add]
      change Multiplicative.ofAdd (↑x.val * c + ↑y.val * d) = Multiplicative.ofAdd 0
      apply congrArg Multiplicative.ofAdd
      simpa [ZMod.natCast_zmod_val, add_comm, mul_comm] using hy
  exact hz_ne (α.injective (by simpa using hαz))

theorem order100_E25_mulAut_eq_matrixAut (α : MulAut order100_E25) :
    α = order100_E25_matrixAut
      (α order100_E25_e1).1.toAdd (α order100_E25_e2).1.toAdd
      (α order100_E25_e1).2.toAdd (α order100_E25_e2).2.toAdd
      (order100_E25_mulAut_det_ne_zero α) := by
  apply order100_E25_mulAut_ext
  · rw [order100_E25_matrixAut_e1]
    ext <;> simp
  · rw [order100_E25_matrixAut_e2]
    ext <;> simp

theorem order100_E25_diag_det_ne_zero (u v : (ZMod 5)ˣ) :
    (u : ZMod 5) * (v : ZMod 5) - 0 * 0 ≠ 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simp [mul_ne_zero (Units.ne_zero u) (Units.ne_zero v)]

/-! ### Unit-valued actions on the cyclic subgroup of order `25` -/

/-- A chosen generator of the cyclic unit group `(ZMod 25)ˣ`. -/
noncomputable abbrev order100_u20 : (ZMod 25)ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 25)

theorem order100_u20_pow_twenty : order100_u20 ^ 20 = 1 := by
  decide

theorem order100_unit_pow_four_eq_one_cases (u : (ZMod 25)ˣ) (hu : u ^ 4 = 1) :
    u = 1 ∨ u = order100_u20 ^ 5 ∨ u = order100_u20 ^ 10 ∨
      u = order100_u20 ^ 15 := by
  decide +revert

theorem order100_unit_sq_eq_one_cases (u : (ZMod 25)ˣ) (hu : u ^ 2 = 1) :
    u = 1 ∨ u = order100_u20 ^ 10 := by
  decide +revert

/-- Multiplication by units embeds into the automorphism group of `C₂₅`. -/
theorem order100_unitAutHom_injective : Function.Injective (unitAutHom (p := 25)) := by
  intro u v h
  have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod 25)) =
      unitAutHom v (Multiplicative.ofAdd (1 : ZMod 25)) := by rw [h]
  simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
  exact Units.ext (congrArg Multiplicative.toAdd h1)

/-- Every automorphism of `C₂₅` is multiplication by a unit of `ZMod 25`. -/
theorem order100_mulAut_eq_unitAutHom (σ : MulAut order100_C25) :
    ∃ u : (ZMod 25)ˣ, σ = unitAutHom u := by
  let f : AddAut (ZMod 25) := Multiplicative.toAdd ((MulAutMultiplicative (ZMod 25)) σ)
  let u : (ZMod 25)ˣ := Additive.toMul ((ZMod.AddAutEquivUnits 25) f)
  refine ⟨u, ?_⟩
  ext x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  change Multiplicative.ofAdd (f m) = unitAutHom u (Multiplicative.ofAdd m)
  have hu : Additive.ofMul u = (ZMod.AddAutEquivUnits 25) f := by simp [u]
  have hf : f = (ZMod.AddAutEquivUnits 25).symm (Additive.ofMul u) := by
    symm
    rw [hu]
    exact AddEquiv.symm_apply_apply (ZMod.AddAutEquivUnits 25) f
  rw [hf, unitAutHom_apply]
  simp [ZMod.AddAutEquivUnits_symm_apply, Units.smul_def]

/-- Turn a unit-valued character into the corresponding action on `C₂₅`. -/
noncomputable abbrev order100_c25Action {H : Type} [Group H] (χ : H →* (ZMod 25)ˣ) :
    H →* MulAut order100_C25 :=
  unitAutHom.comp χ

theorem order100_c25Action_one {H : Type} [Group H] :
    order100_c25Action (H := H) 1 = 1 := by
  ext h x
  simp [order100_c25Action]

noncomputable abbrev order100_chiC4_four : order100_C4 →* (ZMod 25)ˣ :=
  powHom (p := 25) (q := 4) (order100_u20 ^ 5) (by decide)

noncomputable abbrev order100_chiC4_two : order100_C4 →* (ZMod 25)ˣ :=
  powHom (p := 25) (q := 4) (order100_u20 ^ 10) (by decide)

/-- The inverse order-`4` character on `C₄`; it is later conjugate to
`order100_chiC4_four` by an automorphism of `C₄`. -/
noncomputable abbrev order100_chiC4_four_inv : order100_C4 →* (ZMod 25)ˣ :=
  powHom (p := 25) (q := 4) (order100_u20 ^ 15) (by decide)

/-- Homomorphisms out of `C₄` are determined by the additive generator `1`. -/
theorem order100_c4_hom_ext {M : Type} [Group M] {χ ψ : order100_C4 →* M}
    (hgen : χ (Multiplicative.ofAdd (1 : ZMod 4)) =
      ψ (Multiplicative.ofAdd (1 : ZMod 4))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  let n : ZMod 4 := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 4)) ^ n.val := by
    rw [show x = Multiplicative.ofAdd n from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 4)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (n.val • (1 : ZMod 4)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 4)) ^ n.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, hgen]

@[simp]
theorem order100_chiC4_four_gen :
    order100_chiC4_four (Multiplicative.ofAdd (1 : ZMod 4)) =
      order100_u20 ^ 5 := by
  decide

@[simp]
theorem order100_chiC4_two_gen :
    order100_chiC4_two (Multiplicative.ofAdd (1 : ZMod 4)) =
      order100_u20 ^ 10 := by
  decide

@[simp]
theorem order100_chiC4_four_inv_gen :
    order100_chiC4_four_inv (Multiplicative.ofAdd (1 : ZMod 4)) =
      order100_u20 ^ 15 := by
  decide

theorem order100_c4_unit_character_cases (χ : order100_C4 →* (ZMod 25)ˣ) :
    χ = 1 ∨ χ = order100_chiC4_four ∨ χ = order100_chiC4_two ∨
      χ = order100_chiC4_four_inv := by
  let g : order100_C4 := Multiplicative.ofAdd (1 : ZMod 4)
  have hpow : χ g ^ 4 = 1 := by
    rw [← map_pow, show g ^ 4 = 1 by decide, map_one]
  rcases order100_unit_pow_four_eq_one_cases (χ g) hpow with h | h | h | h
  · left
    apply order100_c4_hom_ext
    simp [g, h]
  · right
    left
    apply order100_c4_hom_ext
    rw [h, order100_chiC4_four_gen]
  · right
    right
    left
    apply order100_c4_hom_ext
    rw [h, order100_chiC4_two_gen]
  · right
    right
    right
    apply order100_c4_hom_ext
    rw [h, order100_chiC4_four_inv_gen]

/-- Every action `C₄ → Aut(C₂₅)` is induced by a unit-valued character. -/
theorem order100_c4_c25Action_eq (φ : order100_C4 →* MulAut order100_C25) :
    ∃ χ : order100_C4 →* (ZMod 25)ˣ, φ = order100_c25Action χ := by
  let g : order100_C4 := Multiplicative.ofAdd (1 : ZMod 4)
  obtain ⟨u, huφ⟩ := order100_mulAut_eq_unitAutHom (φ g)
  have hg4 : g ^ 4 = 1 := by decide
  have hφg4 : (φ g) ^ 4 = 1 := by rw [← map_pow, hg4, map_one]
  have hu4 : u ^ 4 = 1 := by
    apply order100_unitAutHom_injective
    rw [map_pow, ← huφ, hφg4]
    exact (map_one (unitAutHom (p := 25))).symm
  refine ⟨powHom (p := 25) (q := 4) u hu4, ?_⟩
  apply order100_c4_hom_ext
  rw [huφ]
  change unitAutHom u = unitAutHom (u ^ (1 : ZMod 4).val)
  rw [show (1 : ZMod 4).val = 1 by decide]
  simp

theorem order100_c4_c25Action_cases (φ : order100_C4 →* MulAut order100_C25) :
    φ = 1 ∨ φ = order100_c25Action order100_chiC4_four ∨
      φ = order100_c25Action order100_chiC4_two ∨
        φ = order100_c25Action order100_chiC4_four_inv := by
  obtain ⟨χ, hφ⟩ := order100_c4_c25Action_eq φ
  rw [hφ]
  rcases order100_c4_unit_character_cases χ with hχ | hχ | hχ | hχ
  · left
    rw [hχ]
    exact order100_c25Action_one
  · right
    left
    rw [hχ]
  · right
    right
    left
    rw [hχ]
  · right
    right
    right
    rw [hχ]

/-- The quotient map `C₂ → (ZMod 25)ˣ` sending the generator to `-1`. -/
noncomputable abbrev order100_c2UnitHom : CyclicRep 2 →* (ZMod 25)ˣ :=
  powHom (p := 25) (q := 2) (order100_u20 ^ 10) (by decide)

@[simp]
theorem order100_c2UnitHom_gen :
    order100_c2UnitHom (Multiplicative.ofAdd (1 : ZMod 2)) =
      order100_u20 ^ 10 := by
  decide

noncomputable abbrev order100_chiV4_fst : order100_V4 →* (ZMod 25)ˣ :=
  order100_c2UnitHom.comp (MonoidHom.fst (CyclicRep 2) (CyclicRep 2))

noncomputable abbrev order100_chiV4_snd : order100_V4 →* (ZMod 25)ˣ :=
  order100_c2UnitHom.comp (MonoidHom.snd (CyclicRep 2) (CyclicRep 2))

noncomputable abbrev order100_chiV4_prod : order100_V4 →* (ZMod 25)ˣ :=
  order100_chiV4_fst * order100_chiV4_snd

/-- Homomorphisms out of `V₄ = C₂ × C₂` are determined by the two standard generators. -/
theorem order100_v4_hom_ext {M : Type} [Group M] {χ ψ : order100_V4 →* M}
    (h1 : χ (Multiplicative.ofAdd (1 : ZMod 2), 1) =
      ψ (Multiplicative.ofAdd (1 : ZMod 2), 1))
    (h2 : χ (1, Multiplicative.ofAdd (1 : ZMod 2)) =
      ψ (1, Multiplicative.ofAdd (1 : ZMod 2))) :
    χ = ψ := by
  apply MonoidHom.ext
  rintro ⟨x1, x2⟩
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x1
  obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective x2
  let g1 : order100_V4 := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let g2 : order100_V4 := (1, Multiplicative.ofAdd (1 : ZMod 2))
  have ha : Multiplicative.ofAdd a = (Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val := by
    calc
      Multiplicative.ofAdd a = Multiplicative.ofAdd ((a.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (a.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ a.val := by rw [ofAdd_nsmul]
  have hb : Multiplicative.ofAdd b = (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.val := by
    calc
      Multiplicative.ofAdd b = Multiplicative.ofAdd ((b.val : ZMod 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (b.val • (1 : ZMod 2)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.val := by rw [ofAdd_nsmul]
  have hx : (Multiplicative.ofAdd a, Multiplicative.ofAdd b) = g1 ^ a.val * g2 ^ b.val := by
    simp [g1, g2, Prod.pow_mk, ha, hb]
  rw [hx, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h1, h2]

@[simp]
theorem order100_chiV4_fst_g1 :
    order100_chiV4_fst (Multiplicative.ofAdd (1 : ZMod 2), 1) =
      order100_u20 ^ 10 := by
  decide

@[simp]
theorem order100_chiV4_fst_g2 :
    order100_chiV4_fst (1, Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  decide

@[simp]
theorem order100_chiV4_snd_g1 :
    order100_chiV4_snd (Multiplicative.ofAdd (1 : ZMod 2), 1) = 1 := by
  decide

@[simp]
theorem order100_chiV4_snd_g2 :
    order100_chiV4_snd (1, Multiplicative.ofAdd (1 : ZMod 2)) =
      order100_u20 ^ 10 := by
  decide

@[simp]
theorem order100_chiV4_prod_g1 :
    order100_chiV4_prod (Multiplicative.ofAdd (1 : ZMod 2), 1) =
      order100_u20 ^ 10 := by
  decide

@[simp]
theorem order100_chiV4_prod_g2 :
    order100_chiV4_prod (1, Multiplicative.ofAdd (1 : ZMod 2)) =
      order100_u20 ^ 10 := by
  decide

theorem order100_v4_unit_character_cases (χ : order100_V4 →* (ZMod 25)ˣ) :
    χ = 1 ∨ χ = order100_chiV4_fst ∨ χ = order100_chiV4_snd ∨
      χ = order100_chiV4_prod := by
  let g1 : order100_V4 := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let g2 : order100_V4 := (1, Multiplicative.ofAdd (1 : ZMod 2))
  have hsq1 : χ g1 ^ 2 = 1 := by
    rw [← map_pow, show g1 ^ 2 = 1 by decide, map_one]
  have hsq2 : χ g2 ^ 2 = 1 := by
    rw [← map_pow, show g2 ^ 2 = 1 by decide, map_one]
  rcases order100_unit_sq_eq_one_cases (χ g1) hsq1 with h1 | h1 <;>
    rcases order100_unit_sq_eq_one_cases (χ g2) hsq2 with h2 | h2
  · left
    apply order100_v4_hom_ext <;>
      simp [g1, g2, h1, h2]
  · right
    right
    left
    apply order100_v4_hom_ext <;>
      simp [g1, g2, h1, h2]
  · right
    left
    apply order100_v4_hom_ext <;>
      simp [g1, g2, h1, h2]
  · right
    right
    right
    apply order100_v4_hom_ext <;>
      simp [g1, g2, h1, h2]

/-- Every action `V₄ → Aut(C₂₅)` is induced by a unit-valued character. -/
theorem order100_v4_c25Action_eq (φ : order100_V4 →* MulAut order100_C25) :
    ∃ χ : order100_V4 →* (ZMod 25)ˣ, φ = order100_c25Action χ := by
  let g1 : order100_V4 := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let g2 : order100_V4 := (1, Multiplicative.ofAdd (1 : ZMod 2))
  obtain ⟨u, huφ⟩ := order100_mulAut_eq_unitAutHom (φ g1)
  obtain ⟨v, hvφ⟩ := order100_mulAut_eq_unitAutHom (φ g2)
  have hg1sq : g1 ^ 2 = 1 := by decide
  have hg2sq : g2 ^ 2 = 1 := by decide
  have hφg1sq : (φ g1) ^ 2 = 1 := by rw [← map_pow, hg1sq, map_one]
  have hφg2sq : (φ g2) ^ 2 = 1 := by rw [← map_pow, hg2sq, map_one]
  have hu2 : u ^ 2 = 1 := by
    apply order100_unitAutHom_injective
    rw [map_pow, ← huφ, hφg1sq]
    exact (map_one (unitAutHom (p := 25))).symm
  have hv2 : v ^ 2 = 1 := by
    apply order100_unitAutHom_injective
    rw [map_pow, ← hvφ, hφg2sq]
    exact (map_one (unitAutHom (p := 25))).symm
  let χ1 : order100_V4 →* (ZMod 25)ˣ :=
    (powHom (p := 25) (q := 2) u hu2).comp (MonoidHom.fst (CyclicRep 2) (CyclicRep 2))
  let χ2 : order100_V4 →* (ZMod 25)ˣ :=
    (powHom (p := 25) (q := 2) v hv2).comp (MonoidHom.snd (CyclicRep 2) (CyclicRep 2))
  refine ⟨χ1 * χ2, ?_⟩
  apply order100_v4_hom_ext
  · rw [huφ]
    change unitAutHom u = unitAutHom ((χ1 * χ2) g1)
    change unitAutHom u = unitAutHom (u ^ (1 : ZMod 2).val * v ^ (0 : ZMod 2).val)
    rw [show (1 : ZMod 2).val = 1 by decide, show (0 : ZMod 2).val = 0 by decide]
    simp
  · rw [hvφ]
    change unitAutHom v = unitAutHom ((χ1 * χ2) g2)
    change unitAutHom v = unitAutHom (u ^ (0 : ZMod 2).val * v ^ (1 : ZMod 2).val)
    rw [show (1 : ZMod 2).val = 1 by decide, show (0 : ZMod 2).val = 0 by decide]
    simp

theorem order100_v4_c25Action_cases (φ : order100_V4 →* MulAut order100_C25) :
    φ = 1 ∨ φ = order100_c25Action order100_chiV4_fst ∨
      φ = order100_c25Action order100_chiV4_snd ∨
        φ = order100_c25Action order100_chiV4_prod := by
  obtain ⟨χ, hφ⟩ := order100_v4_c25Action_eq φ
  rw [hφ]
  rcases order100_v4_unit_character_cases χ with hχ | hχ | hχ | hχ
  · left
    rw [hχ]
    exact order100_c25Action_one
  · right
    left
    rw [hχ]
  · right
    right
    left
    rw [hχ]
  · right
    right
    right
    rw [hχ]

/-! ### Diagonal actions on the elementary-abelian subgroup of order `25` -/

/-- A chosen element of order `4` in `(ZMod 5)ˣ`. -/
noncomputable abbrev order100_u5_4 : (ZMod 5)ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 5)

theorem order100_u5_4_pow_four : order100_u5_4 ^ 4 = 1 := by
  decide

theorem order100_zmod5_unit_cases (u : (ZMod 5)ˣ) :
    u = 1 ∨ u = order100_u5_4 ∨ u = order100_u5_4 ^ 2 ∨
      u = order100_u5_4 ^ 3 := by
  decide +revert

theorem order100_zmod5_unit_sq_eq_one_cases (u : (ZMod 5)ˣ) (hu : u ^ 2 = 1) :
    u = 1 ∨ u = order100_u5_4 ^ 2 := by
  decide +revert

/-- The diagonal automorphism of `(C₅)²` multiplying the two coordinates by `u` and `v`. -/
noncomputable abbrev order100_e25DiagAut (u v : (ZMod 5)ˣ) : MulAut order100_E25 :=
  MulEquiv.prodCongr (unitAutHom u) (unitAutHom v)

theorem order100_E25_matrixAut_diag_eq (u v : (ZMod 5)ˣ)
    (hdet : (u : ZMod 5) * (v : ZMod 5) - 0 * 0 ≠ 0) :
    order100_E25_matrixAut (u : ZMod 5) 0 0 (v : ZMod 5) hdet =
      order100_e25DiagAut u v := by
  apply order100_E25_mulAut_ext
  · rw [order100_E25_matrixAut_e1]
    change (Multiplicative.ofAdd (u : ZMod 5), 1) =
      (unitAutHom u (Multiplicative.ofAdd (1 : ZMod 5)), unitAutHom v 1)
    apply Prod.ext
    · rw [unitAutHom_apply]
      simp
    · exact (map_one (unitAutHom v)).symm
  · rw [order100_E25_matrixAut_e2]
    change (1, Multiplicative.ofAdd (v : ZMod 5)) =
      (unitAutHom u 1, unitAutHom v (Multiplicative.ofAdd (1 : ZMod 5)))
    apply Prod.ext
    · exact (map_one (unitAutHom u)).symm
    · rw [unitAutHom_apply]
      simp

/-- Diagonal automorphisms form a subgroup of `Aut((C₅)²)`, parametrised by two units. -/
noncomputable def order100_e25DiagAutHom : (ZMod 5)ˣ × (ZMod 5)ˣ →* MulAut order100_E25 where
  toFun uv := order100_e25DiagAut uv.1 uv.2
  map_one' := by
    ext x
    · change (unitAutHom (p := 5) 1) x.1 = x.1
      rw [map_one]
      rfl
    · change (unitAutHom (p := 5) 1) x.2 = x.2
      rw [map_one]
      rfl
  map_mul' uv uw := by
    ext x
    · change unitAutHom (uv.1 * uw.1) x.1 = (unitAutHom uv.1 * unitAutHom uw.1) x.1
      rw [map_mul]
    · change unitAutHom (uv.2 * uw.2) x.2 = (unitAutHom uv.2 * unitAutHom uw.2) x.2
      rw [map_mul]

/-- A pair of unit-valued characters gives a diagonal action on `(C₅)²`. -/
noncomputable abbrev order100_e25DiagAction {H : Type} [Group H]
    (χ₁ χ₂ : H →* (ZMod 5)ˣ) : H →* MulAut order100_E25 :=
  order100_e25DiagAutHom.comp (χ₁.prod χ₂)

theorem order100_e25DiagAction_one {H : Type} [Group H] :
    order100_e25DiagAction (H := H) 1 1 = 1 := by
  ext h x
  · change (unitAutHom (p := 5) 1) x.1 = x.1
    rw [map_one]
    rfl
  · change (unitAutHom (p := 5) 1) x.2 = x.2
    rw [map_one]
    rfl

theorem order100_e25DiagAction_comp {H K : Type} [Group H] [Group K]
    (χ₁ χ₂ : H →* (ZMod 5)ˣ) (σ : K →* H) :
    (order100_e25DiagAction χ₁ χ₂).comp σ =
      order100_e25DiagAction (χ₁.comp σ) (χ₂.comp σ) := by
  rfl

/-- Swap the two cyclic factors of `(C₅)²`. -/
noncomputable def order100_E25_swap : order100_E25 ≃* order100_E25 where
  toFun x := (x.2, x.1)
  invFun x := (x.2, x.1)
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_mul' x y := by rfl

theorem order100_e25DiagAut_swap_conj (u v : (ZMod 5)ˣ) :
    (MulAut.conj order100_E25_swap) (order100_e25DiagAut u v) =
      order100_e25DiagAut v u := by
  ext x <;> rfl

theorem order100_e25DiagAction_swap_conj {H : Type} [Group H]
    (χ₁ χ₂ : H →* (ZMod 5)ˣ) :
    (MulAut.conj order100_E25_swap).toMonoidHom.comp (order100_e25DiagAction χ₁ χ₂) =
      order100_e25DiagAction χ₂ χ₁ := by
  ext h x <;> rfl

/-- Swapping the two `C₅` factors identifies the two diagonal actions with exchanged characters. -/
noncomputable def order100_e25DiagAction_swap_mulEquiv {H : Type} [Group H]
    (χ₁ χ₂ : H →* (ZMod 5)ˣ) :
    SemidirectProduct order100_E25 H (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 H (order100_e25DiagAction χ₂ χ₁) :=
  (semidirectProductCongrConj order100_E25_swap).trans
    (semidirectProductCongr_eq (order100_e25DiagAction_swap_conj χ₁ χ₂))

/-- Precomposing both characters by an automorphism of the complement does not change the
semidirect product up to isomorphism. -/
noncomputable def order100_e25DiagAction_precomp_mulEquiv {H : Type} [Group H]
    (χ₁ χ₂ : H →* (ZMod 5)ˣ) (σ : H ≃* H) :
    SemidirectProduct order100_E25 H
        (order100_e25DiagAction (χ₁.comp σ.toMonoidHom) (χ₂.comp σ.toMonoidHom)) ≃*
      SemidirectProduct order100_E25 H (order100_e25DiagAction χ₁ χ₂) :=
  semidirectProductCongrAut (N := order100_E25) (H := H)
    (φ := order100_e25DiagAction χ₁ χ₂) σ

theorem order100_zmod5_character_one_comp {H : Type} [Group H] (σ : H ≃* H) :
    (1 : H →* (ZMod 5)ˣ).comp σ.toMonoidHom = 1 := by
  ext h
  rfl

noncomputable def order100_e25DiagAction_precomp_pair_mulEquiv {H : Type} [Group H]
    (χ₁ χ₂ ψ₁ ψ₂ : H →* (ZMod 5)ˣ) (σ : H ≃* H)
    (h₁ : χ₁.comp σ.toMonoidHom = ψ₁) (h₂ : χ₂.comp σ.toMonoidHom = ψ₂) :
    SemidirectProduct order100_E25 H (order100_e25DiagAction ψ₁ ψ₂) ≃*
      SemidirectProduct order100_E25 H (order100_e25DiagAction χ₁ χ₂) := by
  have haction :
      order100_e25DiagAction ψ₁ ψ₂ =
        order100_e25DiagAction (χ₁.comp σ.toMonoidHom) (χ₂.comp σ.toMonoidHom) := by
    rw [h₁, h₂]
  exact (semidirectProductCongr_eq haction).trans
    (order100_e25DiagAction_precomp_mulEquiv χ₁ χ₂ σ)

noncomputable abbrev order100_chi5C4_four : order100_C4 →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 4) order100_u5_4 (by decide)

noncomputable abbrev order100_chi5C4_two : order100_C4 →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 4) (order100_u5_4 ^ 2) (by decide)

noncomputable abbrev order100_chi5C4_four_inv : order100_C4 →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 4) (order100_u5_4 ^ 3) (by decide)

@[simp]
theorem order100_chi5C4_four_gen :
    order100_chi5C4_four (Multiplicative.ofAdd (1 : ZMod 4)) = order100_u5_4 := by
  decide

@[simp]
theorem order100_chi5C4_two_gen :
    order100_chi5C4_two (Multiplicative.ofAdd (1 : ZMod 4)) =
      order100_u5_4 ^ 2 := by
  decide

@[simp]
theorem order100_chi5C4_four_inv_gen :
    order100_chi5C4_four_inv (Multiplicative.ofAdd (1 : ZMod 4)) =
      order100_u5_4 ^ 3 := by
  decide

theorem order100_c4_zmod5_character_cases (χ : order100_C4 →* (ZMod 5)ˣ) :
    χ = 1 ∨ χ = order100_chi5C4_four ∨ χ = order100_chi5C4_two ∨
      χ = order100_chi5C4_four_inv := by
  let g : order100_C4 := Multiplicative.ofAdd (1 : ZMod 4)
  have hpow : χ g ^ 4 = 1 := by
    rw [← map_pow, show g ^ 4 = 1 by decide, map_one]
  rcases order100_zmod5_unit_cases (χ g) with h | h | h | h
  · left
    apply order100_c4_hom_ext
    simp [g, h]
  · right
    left
    apply order100_c4_hom_ext
    rw [h, order100_chi5C4_four_gen]
  · right
    right
    left
    apply order100_c4_hom_ext
    rw [h, order100_chi5C4_two_gen]
  · right
    right
    right
    apply order100_c4_hom_ext
    rw [h, order100_chi5C4_four_inv_gen]

/-- The automorphism of `C₄` sending the additive generator to three times itself. -/
noncomputable def order100_C4_mulThree : order100_C4 ≃* order100_C4 :=
  unitAutHom (p := 4) (ZMod.unitOfCoprime 3 (by norm_num : Nat.Coprime 3 4))

theorem order100_chi5C4_four_comp_mulThree :
    order100_chi5C4_four.comp order100_C4_mulThree.toMonoidHom =
      order100_chi5C4_four_inv := by
  apply order100_c4_hom_ext
  decide

theorem order100_chi5C4_four_inv_comp_mulThree :
    order100_chi5C4_four_inv.comp order100_C4_mulThree.toMonoidHom =
      order100_chi5C4_four := by
  apply order100_c4_hom_ext
  decide

theorem order100_chi5C4_two_comp_mulThree :
    order100_chi5C4_two.comp order100_C4_mulThree.toMonoidHom =
      order100_chi5C4_two := by
  apply order100_c4_hom_ext
  decide

theorem order100_chi5C4_one_comp_mulThree :
    (1 : order100_C4 →* (ZMod 5)ˣ).comp order100_C4_mulThree.toMonoidHom = 1 := by
  apply order100_c4_hom_ext
  decide

noncomputable abbrev order100_c2UnitHom5 : CyclicRep 2 →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 2) (order100_u5_4 ^ 2) (by decide)

@[simp]
theorem order100_c2UnitHom5_gen :
    order100_c2UnitHom5 (Multiplicative.ofAdd (1 : ZMod 2)) =
      order100_u5_4 ^ 2 := by
  decide

noncomputable abbrev order100_chi5V4_fst : order100_V4 →* (ZMod 5)ˣ :=
  order100_c2UnitHom5.comp (MonoidHom.fst (CyclicRep 2) (CyclicRep 2))

noncomputable abbrev order100_chi5V4_snd : order100_V4 →* (ZMod 5)ˣ :=
  order100_c2UnitHom5.comp (MonoidHom.snd (CyclicRep 2) (CyclicRep 2))

noncomputable abbrev order100_chi5V4_prod : order100_V4 →* (ZMod 5)ˣ :=
  order100_chi5V4_fst * order100_chi5V4_snd

@[simp]
theorem order100_chi5V4_fst_g1 :
    order100_chi5V4_fst (Multiplicative.ofAdd (1 : ZMod 2), 1) =
      order100_u5_4 ^ 2 := by
  decide

@[simp]
theorem order100_chi5V4_fst_g2 :
    order100_chi5V4_fst (1, Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  decide

@[simp]
theorem order100_chi5V4_snd_g1 :
    order100_chi5V4_snd (Multiplicative.ofAdd (1 : ZMod 2), 1) = 1 := by
  decide

@[simp]
theorem order100_chi5V4_snd_g2 :
    order100_chi5V4_snd (1, Multiplicative.ofAdd (1 : ZMod 2)) =
      order100_u5_4 ^ 2 := by
  decide

@[simp]
theorem order100_chi5V4_prod_g1 :
    order100_chi5V4_prod (Multiplicative.ofAdd (1 : ZMod 2), 1) =
      order100_u5_4 ^ 2 := by
  decide

@[simp]
theorem order100_chi5V4_prod_g2 :
    order100_chi5V4_prod (1, Multiplicative.ofAdd (1 : ZMod 2)) =
      order100_u5_4 ^ 2 := by
  decide

theorem order100_v4_zmod5_character_cases (χ : order100_V4 →* (ZMod 5)ˣ) :
    χ = 1 ∨ χ = order100_chi5V4_fst ∨ χ = order100_chi5V4_snd ∨
      χ = order100_chi5V4_prod := by
  let g1 : order100_V4 := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  let g2 : order100_V4 := (1, Multiplicative.ofAdd (1 : ZMod 2))
  have hsq1 : χ g1 ^ 2 = 1 := by
    rw [← map_pow, show g1 ^ 2 = 1 by decide, map_one]
  have hsq2 : χ g2 ^ 2 = 1 := by
    rw [← map_pow, show g2 ^ 2 = 1 by decide, map_one]
  rcases order100_zmod5_unit_sq_eq_one_cases (χ g1) hsq1 with h1 | h1 <;>
    rcases order100_zmod5_unit_sq_eq_one_cases (χ g2) hsq2 with h2 | h2
  · left
    apply order100_v4_hom_ext <;>
      simp [g1, g2, h1, h2]
  · right
    right
    left
    apply order100_v4_hom_ext <;>
      simp [g1, g2, h1, h2]
  · right
    left
    apply order100_v4_hom_ext <;>
      simp [g1, g2, h1, h2]
  · right
    right
    right
    apply order100_v4_hom_ext <;>
      simp [g1, g2, h1, h2]

theorem order100_c2_mul_self (x : CyclicRep 2) : x * x = 1 := by
  decide +revert

/-- Swap the two factors of `V₄ = C₂ × C₂`. -/
noncomputable def order100_V4_swap : order100_V4 ≃* order100_V4 where
  toFun x := (x.2, x.1)
  invFun x := (x.2, x.1)
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_mul' x y := by rfl

/-- The shear `(x, y) ↦ (x, xy)` of `V₄ = C₂ × C₂`. -/
noncomputable def order100_V4_shear : order100_V4 ≃* order100_V4 where
  toFun x := (x.1, x.1 * x.2)
  invFun x := (x.1, x.1 * x.2)
  left_inv x := by
    ext
    · rfl
    · change x.1 * (x.1 * x.2) = x.2
      rw [← mul_assoc, order100_c2_mul_self x.1, one_mul]
  right_inv x := by
    ext
    · rfl
    · change x.1 * (x.1 * x.2) = x.2
      rw [← mul_assoc, order100_c2_mul_self x.1, one_mul]
  map_mul' x y := by ext <;> simp [mul_comm, mul_left_comm]

theorem order100_chi5V4_fst_comp_swap :
    order100_chi5V4_fst.comp order100_V4_swap.toMonoidHom = order100_chi5V4_snd := by
  apply order100_v4_hom_ext <;> decide

theorem order100_chi5V4_snd_comp_swap :
    order100_chi5V4_snd.comp order100_V4_swap.toMonoidHom = order100_chi5V4_fst := by
  apply order100_v4_hom_ext <;> decide

theorem order100_chi5V4_fst_comp_shear :
    order100_chi5V4_fst.comp order100_V4_shear.toMonoidHom = order100_chi5V4_fst := by
  apply order100_v4_hom_ext <;> decide

theorem order100_chi5V4_snd_comp_shear :
    order100_chi5V4_snd.comp order100_V4_shear.toMonoidHom = order100_chi5V4_prod := by
  apply order100_v4_hom_ext <;> decide

theorem order100_chi5V4_prod_comp_shear :
    order100_chi5V4_prod.comp order100_V4_shear.toMonoidHom = order100_chi5V4_snd := by
  apply order100_v4_hom_ext <;> decide

noncomputable def order100_V4_toProd : order100_V4 ≃* order100_V4 :=
  order100_V4_shear.trans order100_V4_swap

noncomputable def order100_V4_toSndProd : order100_V4 ≃* order100_V4 :=
  order100_V4_swap.trans order100_V4_shear

theorem order100_chi5V4_fst_comp_toProd :
    order100_chi5V4_fst.comp order100_V4_toProd.toMonoidHom = order100_chi5V4_prod := by
  apply order100_v4_hom_ext <;> decide

theorem order100_chi5V4_snd_comp_toProd :
    order100_chi5V4_snd.comp order100_V4_toProd.toMonoidHom = order100_chi5V4_fst := by
  apply order100_v4_hom_ext <;> decide

theorem order100_chi5V4_fst_comp_toSndProd :
    order100_chi5V4_fst.comp order100_V4_toSndProd.toMonoidHom = order100_chi5V4_snd := by
  apply order100_v4_hom_ext <;> decide

theorem order100_chi5V4_snd_comp_toSndProd :
    order100_chi5V4_snd.comp order100_V4_toSndProd.toMonoidHom = order100_chi5V4_prod := by
  apply order100_v4_hom_ext <;> decide

/-! The expected diagonal standard actions for the elementary-abelian `25`-subgroup.

For `C₄`, the suffix records the two character exponents, with `4` denoting
`order100_chi5C4_four`, `2` denoting its square, and `4i` denoting its inverse.
The seven displayed cases are the diagonal representatives expected after swapping
the two factors and inverting the generator of `C₄`.
-/

noncomputable abbrev order100_e25C4_00 : order100_C4 →* MulAut order100_E25 :=
  order100_e25DiagAction 1 1

noncomputable abbrev order100_e25C4_20 : order100_C4 →* MulAut order100_E25 :=
  order100_e25DiagAction order100_chi5C4_two 1

noncomputable abbrev order100_e25C4_40 : order100_C4 →* MulAut order100_E25 :=
  order100_e25DiagAction order100_chi5C4_four 1

noncomputable abbrev order100_e25C4_22 : order100_C4 →* MulAut order100_E25 :=
  order100_e25DiagAction order100_chi5C4_two order100_chi5C4_two

noncomputable abbrev order100_e25C4_42 : order100_C4 →* MulAut order100_E25 :=
  order100_e25DiagAction order100_chi5C4_four order100_chi5C4_two

noncomputable abbrev order100_e25C4_44 : order100_C4 →* MulAut order100_E25 :=
  order100_e25DiagAction order100_chi5C4_four order100_chi5C4_four

noncomputable abbrev order100_e25C4_44i : order100_C4 →* MulAut order100_E25 :=
  order100_e25DiagAction order100_chi5C4_four order100_chi5C4_four_inv

noncomputable def order100_e25C4_four_inv_one_equiv_40 :
    SemidirectProduct order100_E25 order100_C4
        (order100_e25DiagAction order100_chi5C4_four_inv 1) ≃*
      SemidirectProduct order100_E25 order100_C4 order100_e25C4_40 := by
  have haction :
      order100_e25DiagAction order100_chi5C4_four_inv 1 =
        order100_e25DiagAction
          (order100_chi5C4_four.comp order100_C4_mulThree.toMonoidHom)
          ((1 : order100_C4 →* (ZMod 5)ˣ).comp order100_C4_mulThree.toMonoidHom) := by
    rw [order100_chi5C4_four_comp_mulThree, order100_chi5C4_one_comp_mulThree]
  exact (semidirectProductCongr_eq haction).trans
    (order100_e25DiagAction_precomp_mulEquiv order100_chi5C4_four 1 order100_C4_mulThree)

noncomputable def order100_e25C4_four_inv_two_equiv_42 :
    SemidirectProduct order100_E25 order100_C4
        (order100_e25DiagAction order100_chi5C4_four_inv order100_chi5C4_two) ≃*
      SemidirectProduct order100_E25 order100_C4 order100_e25C4_42 := by
  have haction :
      order100_e25DiagAction order100_chi5C4_four_inv order100_chi5C4_two =
        order100_e25DiagAction
          (order100_chi5C4_four.comp order100_C4_mulThree.toMonoidHom)
          (order100_chi5C4_two.comp order100_C4_mulThree.toMonoidHom) := by
    rw [order100_chi5C4_four_comp_mulThree, order100_chi5C4_two_comp_mulThree]
  exact (semidirectProductCongr_eq haction).trans
    (order100_e25DiagAction_precomp_mulEquiv order100_chi5C4_four order100_chi5C4_two
      order100_C4_mulThree)

noncomputable def order100_e25C4_two_four_inv_equiv_42 :
    SemidirectProduct order100_E25 order100_C4
        (order100_e25DiagAction order100_chi5C4_two order100_chi5C4_four_inv) ≃*
      SemidirectProduct order100_E25 order100_C4 order100_e25C4_42 := by
  have haction :
      order100_e25DiagAction order100_chi5C4_two order100_chi5C4_four_inv =
        order100_e25DiagAction
          (order100_chi5C4_two.comp order100_C4_mulThree.toMonoidHom)
          (order100_chi5C4_four.comp order100_C4_mulThree.toMonoidHom) := by
    rw [order100_chi5C4_two_comp_mulThree, order100_chi5C4_four_comp_mulThree]
  exact ((semidirectProductCongr_eq haction).trans
    (order100_e25DiagAction_precomp_mulEquiv order100_chi5C4_two order100_chi5C4_four
      order100_C4_mulThree)).trans
    (order100_e25DiagAction_swap_mulEquiv order100_chi5C4_two order100_chi5C4_four)

noncomputable def order100_e25C4_four_inv_four_inv_equiv_44 :
    SemidirectProduct order100_E25 order100_C4
        (order100_e25DiagAction order100_chi5C4_four_inv order100_chi5C4_four_inv) ≃*
      SemidirectProduct order100_E25 order100_C4 order100_e25C4_44 := by
  have haction :
      order100_e25DiagAction order100_chi5C4_four_inv order100_chi5C4_four_inv =
        order100_e25DiagAction
          (order100_chi5C4_four.comp order100_C4_mulThree.toMonoidHom)
          (order100_chi5C4_four.comp order100_C4_mulThree.toMonoidHom) := by
    rw [order100_chi5C4_four_comp_mulThree]
  exact (semidirectProductCongr_eq haction).trans
    (order100_e25DiagAction_precomp_mulEquiv order100_chi5C4_four order100_chi5C4_four
      order100_C4_mulThree)

theorem order100_e25C4_diagAction_cases (χ₁ χ₂ : order100_C4 →* (ZMod 5)ˣ) :
    Nonempty (SemidirectProduct order100_E25 order100_C4 (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 order100_C4 order100_e25C4_00) ∨
    Nonempty (SemidirectProduct order100_E25 order100_C4 (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 order100_C4 order100_e25C4_20) ∨
    Nonempty (SemidirectProduct order100_E25 order100_C4 (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 order100_C4 order100_e25C4_40) ∨
    Nonempty (SemidirectProduct order100_E25 order100_C4 (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 order100_C4 order100_e25C4_22) ∨
    Nonempty (SemidirectProduct order100_E25 order100_C4 (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 order100_C4 order100_e25C4_42) ∨
    Nonempty (SemidirectProduct order100_E25 order100_C4 (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 order100_C4 order100_e25C4_44) ∨
    Nonempty (SemidirectProduct order100_E25 order100_C4 (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 order100_C4 order100_e25C4_44i) := by
  rcases order100_c4_zmod5_character_cases χ₁ with h₁ | h₁ | h₁ | h₁ <;>
    rcases order100_c4_zmod5_character_cases χ₂ with h₂ | h₂ | h₂ | h₂
  · subst χ₁; subst χ₂
    left
    exact ⟨MulEquiv.refl _⟩
  · subst χ₁; subst χ₂
    right; right; left
    exact ⟨order100_e25DiagAction_swap_mulEquiv 1 order100_chi5C4_four⟩
  · subst χ₁; subst χ₂
    right; left
    exact ⟨order100_e25DiagAction_swap_mulEquiv 1 order100_chi5C4_two⟩
  · subst χ₁; subst χ₂
    right; right; left
    exact ⟨(order100_e25DiagAction_swap_mulEquiv 1 order100_chi5C4_four_inv).trans
      order100_e25C4_four_inv_one_equiv_40⟩
  · subst χ₁; subst χ₂
    right; right; left
    exact ⟨MulEquiv.refl _⟩
  · subst χ₁; subst χ₂
    right; right; right; right; right; left
    exact ⟨MulEquiv.refl _⟩
  · subst χ₁; subst χ₂
    right; right; right; right; left
    exact ⟨MulEquiv.refl _⟩
  · subst χ₁; subst χ₂
    right; right; right; right; right; right
    exact ⟨MulEquiv.refl _⟩
  · subst χ₁; subst χ₂
    right; left
    exact ⟨MulEquiv.refl _⟩
  · subst χ₁; subst χ₂
    right; right; right; right; left
    exact ⟨order100_e25DiagAction_swap_mulEquiv order100_chi5C4_two order100_chi5C4_four⟩
  · subst χ₁; subst χ₂
    right; right; right; left
    exact ⟨MulEquiv.refl _⟩
  · subst χ₁; subst χ₂
    right; right; right; right; left
    exact ⟨order100_e25C4_two_four_inv_equiv_42⟩
  · subst χ₁; subst χ₂
    right; right; left
    exact ⟨order100_e25C4_four_inv_one_equiv_40⟩
  · subst χ₁; subst χ₂
    right; right; right; right; right; right
    exact ⟨order100_e25DiagAction_swap_mulEquiv order100_chi5C4_four_inv order100_chi5C4_four⟩
  · subst χ₁; subst χ₂
    right; right; right; right; left
    exact ⟨order100_e25C4_four_inv_two_equiv_42⟩
  · subst χ₁; subst χ₂
    right; right; right; right; right; left
    exact ⟨order100_e25C4_four_inv_four_inv_equiv_44⟩

/-! For `V₄`, the four diagonal representatives are: no non-trivial character, one character,
the same character twice, and two independent characters. -/

noncomputable abbrev order100_e25V4_00 : order100_V4 →* MulAut order100_E25 :=
  order100_e25DiagAction 1 1

noncomputable abbrev order100_e25V4_10 : order100_V4 →* MulAut order100_E25 :=
  order100_e25DiagAction order100_chi5V4_fst 1

noncomputable abbrev order100_e25V4_11 : order100_V4 →* MulAut order100_E25 :=
  order100_e25DiagAction order100_chi5V4_fst order100_chi5V4_fst

noncomputable abbrev order100_e25V4_12 : order100_V4 →* MulAut order100_E25 :=
  order100_e25DiagAction order100_chi5V4_fst order100_chi5V4_snd

noncomputable def order100_e25V4_snd_one_equiv_10 :
    SemidirectProduct order100_E25 order100_V4
        (order100_e25DiagAction order100_chi5V4_snd 1) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_10 :=
  order100_e25DiagAction_precomp_pair_mulEquiv order100_chi5V4_fst 1
    order100_chi5V4_snd 1 order100_V4_swap order100_chi5V4_fst_comp_swap
    (order100_zmod5_character_one_comp order100_V4_swap)

noncomputable def order100_e25V4_prod_one_equiv_10 :
    SemidirectProduct order100_E25 order100_V4
        (order100_e25DiagAction order100_chi5V4_prod 1) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_10 :=
  order100_e25DiagAction_precomp_pair_mulEquiv order100_chi5V4_fst 1
    order100_chi5V4_prod 1 order100_V4_toProd order100_chi5V4_fst_comp_toProd
    (order100_zmod5_character_one_comp order100_V4_toProd)

noncomputable def order100_e25V4_snd_snd_equiv_11 :
    SemidirectProduct order100_E25 order100_V4
        (order100_e25DiagAction order100_chi5V4_snd order100_chi5V4_snd) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_11 :=
  order100_e25DiagAction_precomp_pair_mulEquiv order100_chi5V4_fst order100_chi5V4_fst
    order100_chi5V4_snd order100_chi5V4_snd order100_V4_swap
    order100_chi5V4_fst_comp_swap order100_chi5V4_fst_comp_swap

noncomputable def order100_e25V4_prod_prod_equiv_11 :
    SemidirectProduct order100_E25 order100_V4
        (order100_e25DiagAction order100_chi5V4_prod order100_chi5V4_prod) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_11 :=
  order100_e25DiagAction_precomp_pair_mulEquiv order100_chi5V4_fst order100_chi5V4_fst
    order100_chi5V4_prod order100_chi5V4_prod order100_V4_toProd
    order100_chi5V4_fst_comp_toProd order100_chi5V4_fst_comp_toProd

noncomputable def order100_e25V4_fst_prod_equiv_12 :
    SemidirectProduct order100_E25 order100_V4
        (order100_e25DiagAction order100_chi5V4_fst order100_chi5V4_prod) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_12 :=
  order100_e25DiagAction_precomp_pair_mulEquiv order100_chi5V4_fst order100_chi5V4_snd
    order100_chi5V4_fst order100_chi5V4_prod order100_V4_shear
    order100_chi5V4_fst_comp_shear order100_chi5V4_snd_comp_shear

noncomputable def order100_e25V4_snd_prod_equiv_12 :
    SemidirectProduct order100_E25 order100_V4
        (order100_e25DiagAction order100_chi5V4_snd order100_chi5V4_prod) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_12 :=
  order100_e25DiagAction_precomp_pair_mulEquiv order100_chi5V4_fst order100_chi5V4_snd
    order100_chi5V4_snd order100_chi5V4_prod order100_V4_toSndProd
    order100_chi5V4_fst_comp_toSndProd order100_chi5V4_snd_comp_toSndProd

noncomputable def order100_e25V4_prod_fst_equiv_12 :
    SemidirectProduct order100_E25 order100_V4
        (order100_e25DiagAction order100_chi5V4_prod order100_chi5V4_fst) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_12 :=
  order100_e25DiagAction_precomp_pair_mulEquiv order100_chi5V4_fst order100_chi5V4_snd
    order100_chi5V4_prod order100_chi5V4_fst order100_V4_toProd
    order100_chi5V4_fst_comp_toProd order100_chi5V4_snd_comp_toProd

noncomputable def order100_e25V4_prod_snd_equiv_12 :
    SemidirectProduct order100_E25 order100_V4
        (order100_e25DiagAction order100_chi5V4_prod order100_chi5V4_snd) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_12 :=
  (order100_e25DiagAction_swap_mulEquiv order100_chi5V4_prod order100_chi5V4_snd).trans
    order100_e25V4_snd_prod_equiv_12

theorem order100_e25V4_diagAction_cases (χ₁ χ₂ : order100_V4 →* (ZMod 5)ˣ) :
    Nonempty (SemidirectProduct order100_E25 order100_V4 (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_00) ∨
    Nonempty (SemidirectProduct order100_E25 order100_V4 (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_10) ∨
    Nonempty (SemidirectProduct order100_E25 order100_V4 (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_11) ∨
    Nonempty (SemidirectProduct order100_E25 order100_V4 (order100_e25DiagAction χ₁ χ₂) ≃*
      SemidirectProduct order100_E25 order100_V4 order100_e25V4_12) := by
  rcases order100_v4_zmod5_character_cases χ₁ with h₁ | h₁ | h₁ | h₁ <;>
    rcases order100_v4_zmod5_character_cases χ₂ with h₂ | h₂ | h₂ | h₂
  · subst χ₁; subst χ₂
    left
    exact ⟨MulEquiv.refl _⟩
  · subst χ₁; subst χ₂
    right; left
    exact ⟨order100_e25DiagAction_swap_mulEquiv 1 order100_chi5V4_fst⟩
  · subst χ₁; subst χ₂
    right; left
    exact ⟨(order100_e25DiagAction_swap_mulEquiv 1 order100_chi5V4_snd).trans
      order100_e25V4_snd_one_equiv_10⟩
  · subst χ₁; subst χ₂
    right; left
    exact ⟨(order100_e25DiagAction_swap_mulEquiv 1 order100_chi5V4_prod).trans
      order100_e25V4_prod_one_equiv_10⟩
  · subst χ₁; subst χ₂
    right; left
    exact ⟨MulEquiv.refl _⟩
  · subst χ₁; subst χ₂
    right; right; left
    exact ⟨MulEquiv.refl _⟩
  · subst χ₁; subst χ₂
    right; right; right
    exact ⟨MulEquiv.refl _⟩
  · subst χ₁; subst χ₂
    right; right; right
    exact ⟨order100_e25V4_fst_prod_equiv_12⟩
  · subst χ₁; subst χ₂
    right; left
    exact ⟨order100_e25V4_snd_one_equiv_10⟩
  · subst χ₁; subst χ₂
    right; right; right
    exact ⟨order100_e25DiagAction_swap_mulEquiv order100_chi5V4_snd order100_chi5V4_fst⟩
  · subst χ₁; subst χ₂
    right; right; left
    exact ⟨order100_e25V4_snd_snd_equiv_11⟩
  · subst χ₁; subst χ₂
    right; right; right
    exact ⟨order100_e25V4_snd_prod_equiv_12⟩
  · subst χ₁; subst χ₂
    right; left
    exact ⟨order100_e25V4_prod_one_equiv_10⟩
  · subst χ₁; subst χ₂
    right; right; right
    exact ⟨order100_e25V4_prod_fst_equiv_12⟩
  · subst χ₁; subst χ₂
    right; right; right
    exact ⟨order100_e25V4_prod_snd_equiv_12⟩
  · subst χ₁; subst χ₂
    right; right; left
    exact ⟨order100_e25V4_prod_prod_equiv_11⟩

/-- Every group of order `100` is one of the four standard semidirect-product action problems:
`C₂₅ ⋊ C₄`, `C₂₅ ⋊ V₄`, `(C₅)² ⋊ C₄`, or `(C₅)² ⋊ V₄`. -/
theorem order100_semidirectProduct_standard_cases [Finite G] (hG : Nat.card G = 100) :
    (∃ φ : order100_C4 →* MulAut order100_C25,
      Nonempty (G ≃* SemidirectProduct order100_C25 order100_C4 φ)) ∨
    (∃ φ : order100_V4 →* MulAut order100_C25,
      Nonempty (G ≃* SemidirectProduct order100_C25 order100_V4 φ)) ∨
    (∃ φ : order100_C4 →* MulAut order100_E25,
      Nonempty (G ≃* SemidirectProduct order100_E25 order100_C4 φ)) ∨
    (∃ φ : order100_V4 →* MulAut order100_E25,
      Nonempty (G ≃* SemidirectProduct order100_E25 order100_V4 φ)) := by
  obtain ⟨P, H, φ, _, hcardP, hcardH, ⟨e⟩⟩ := order100_semidirectProduct hG
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP25 : Nat.card P = 5 ^ 2 := by simpa using hcardP
  have hH4 : Nat.card H = 2 ^ 2 := by simpa using hcardH
  rcases prime_sq_classification (p := 5) hP25 with hPcyc | hPelem
  · have hPcyc' : Nonempty (P ≃* order100_C25) := by simpa [order100_C25] using hPcyc
    obtain ⟨eP⟩ := hPcyc'
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    rcases prime_sq_classification (p := 2) hH4 with hHcyc | hHelem
    · have hHcyc' : Nonempty (H ≃* order100_C4) := by simpa [order100_C4] using hHcyc
      obtain ⟨eH⟩ := hHcyc'
      exact Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' eP eH)⟩⟩
    · have hHelem' : Nonempty (H ≃* order100_V4) := by simpa [order100_V4] using hHelem
      obtain ⟨eH⟩ := hHelem'
      exact Or.inr <| Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' eP eH)⟩⟩
  · have hPelem' : Nonempty (P ≃* order100_E25) := by simpa [order100_E25] using hPelem
    obtain ⟨eP⟩ := hPelem'
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    rcases prime_sq_classification (p := 2) hH4 with hHcyc | hHelem
    · have hHcyc' : Nonempty (H ≃* order100_C4) := by simpa [order100_C4] using hHcyc
      obtain ⟨eH⟩ := hHcyc'
      exact Or.inr <| Or.inr <| Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' eP eH)⟩⟩
    · have hHelem' : Nonempty (H ≃* order100_V4) := by simpa [order100_V4] using hHelem
      obtain ⟨eH⟩ := hHelem'
      exact Or.inr <| Or.inr <| Or.inr ⟨_, ⟨e.trans (SemidirectProduct.congr' eP eH)⟩⟩

end Smallgroups.UsefulTheorems
