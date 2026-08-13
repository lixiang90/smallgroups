/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeKernelTypes
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeCocycleBranch
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionCore
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionOrbits

/-!
# Explicit representatives for the RM action orbits

This module contains the finite coordinate calculations for the concrete
order-three actions. They are separated from `FourSylowThreeRM` so that
iterating on the abstract RM reduction does not re-elaborate every explicit
representative.
-/

namespace Smallgroups.UsefulTheorems

open SemidirectProduct

/-! ### The first concrete RM Wild action: `G₇` -/

/-- The order-three automorphism fixing the `C₄` factor and cycling the two
elementary factors of `G₇ = C₄ × C₂ × C₂`. -/
noncomputable def order48_RM_G7_tau3 : MulAut order16_wild_G7 where
  toFun p := ((p.1.1, p.2), (p.1.2 * p.2))
  invFun p := ((p.1.1, p.1.2 * p.2), p.1.2)
  left_inv := by
    rintro ⟨⟨a, b⟩, c⟩
    ext <;> revert a b c <;> decide
  right_inv := by
    rintro ⟨⟨a, b⟩, c⟩
    ext <;> revert a b c <;> decide
  map_mul' := by
    rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
    ext <;> revert a b c a' b' c' <;> decide

theorem order48_RM_G7_tau3_pow_three :
    order48_RM_G7_tau3 ^ 3 = 1 := by
  apply MulEquiv.ext
  rintro ⟨⟨a, b⟩, c⟩
  revert a b c
  decide

noncomputable def order48_RM_G7_action :
    Multiplicative (ZMod 3) →* MulAut order16_wild_G7 :=
  MonoidHom.mk' (fun x => order48_RM_G7_tau3 ^
    (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add order48_RM_G7_tau3_pow_three a.toAdd b.toAdd)

noncomputable instance order48_RM_G7_action_fintype :
    Fintype (SemidirectProduct order16_wild_G7
      (Multiplicative (ZMod 3)) order48_RM_G7_action) :=
  Fintype.ofEquiv (order16_wild_G7 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

theorem order48_RM_G7_action_card_cube_roots :
    Nat.card {x : SemidirectProduct order16_wild_G7
      (Multiplicative (ZMod 3)) order48_RM_G7_action // x ^ 3 = 1} = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem order48_RM_G7_action_card_sylow_three :
    Nat.card (Sylow 3 (SemidirectProduct order16_wild_G7
      (Multiplicative (ZMod 3)) order48_RM_G7_action)) = 4 :=
  (order48_c3_action_card_sylow_three_eq_four_iff
    (card_order16_wild_G7) order48_RM_G7_action).mpr
    order48_RM_G7_action_card_cube_roots

abbrev order48_RM_E4 :=
  Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

noncomputable def order48_RM_E4_tau3 : MulAut order48_RM_E4 where
  toFun p := (p.2, p.1 * p.2)
  invFun p := (p.1 * p.2, p.1)
  left_inv := by
    rintro ⟨a, b⟩
    ext <;> revert a b <;> decide
  right_inv := by
    rintro ⟨a, b⟩
    ext <;> revert a b <;> decide
  map_mul' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩
    ext <;> revert a b a' b' <;> decide

theorem order48_RM_E4_tau3_pow_three : order48_RM_E4_tau3 ^ 3 = 1 := by
  apply MulEquiv.ext
  rintro ⟨a, b⟩
  revert a b
  decide

noncomputable def order48_RM_E4_action :
    Multiplicative (ZMod 3) →* MulAut order48_RM_E4 :=
  MonoidHom.mk' (fun x => order48_RM_E4_tau3 ^
    (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add order48_RM_E4_tau3_pow_three a.toAdd b.toAdd)

noncomputable instance order48_RM_E4_action_fintype :
    Fintype (SemidirectProduct order48_RM_E4
      (Multiplicative (ZMod 3)) order48_RM_E4_action) :=
  Fintype.ofEquiv (order48_RM_E4 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

noncomputable def order48_RM_G7_splitEquiv :
    SemidirectProduct order16_wild_G7
        (Multiplicative (ZMod 3)) order48_RM_G7_action ≃*
      CyclicRep 4 × SemidirectProduct order48_RM_E4
        (Multiplicative (ZMod 3)) order48_RM_E4_action where
  toFun x := (x.left.1.1,
    ⟨(x.left.1.2, x.left.2), x.right⟩)
  invFun x := ⟨((x.1, x.2.left.1), x.2.left.2), x.2.right⟩
  left_inv := by
    rintro ⟨⟨⟨a, b⟩, c⟩, d⟩
    rfl
  right_inv := by
    rintro ⟨a, ⟨⟨b, c⟩, d⟩⟩
    rfl
  map_mul' := by
    rintro ⟨⟨⟨a, b⟩, c⟩, d⟩ ⟨⟨⟨a', b'⟩, c'⟩, d'⟩
    ext <;> revert a b c d a' b' c' d' <;> decide

theorem order48_RM_G7_action_mulEquiv_C4xA4 :
    Nonempty (SemidirectProduct order16_wild_G7
      (Multiplicative (ZMod 3)) order48_RM_G7_action ≃*
      order48_four_C4xA4) := by
  have hcard : Nat.card (SemidirectProduct order48_RM_E4
      (Multiplicative (ZMod 3)) order48_RM_E4_action) = 12 := by
    rw [SemidirectProduct.card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    decide
  have hroots : Nat.card {x : SemidirectProduct order48_RM_E4
      (Multiplicative (ZMod 3)) order48_RM_E4_action // x ^ 3 = 1} = 9 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hsyl := order48_card_sylow_three_eq_four_of_card_pow_three_eq_one
    hcard hroots
  obtain ⟨eA⟩ := fourP_12_equiv_A4_of_card_sylow_three_eq_four hcard hsyl
  exact ⟨order48_RM_G7_splitEquiv.trans
    (MulEquiv.prodCongr (MulEquiv.refl _) eA)⟩

theorem order48_RM_G7_action_mem_residualKnownReps :
    Nonempty (SemidirectProduct order16_wild_G7
      (Multiplicative (ZMod 3)) order48_RM_G7_action ≃*
      order48_four_residualKnownReps 3) := by
  simpa using order48_RM_G7_action_mulEquiv_C4xA4

/-! ### The quaternion RM kernel `G₁₁` -/

noncomputable def order48_RM_G11_tau3 : MulAut order16_wild_G11 :=
  MulEquiv.prodCongr order24_tau3Q8 (MulEquiv.refl _)

theorem order48_RM_G11_tau3_pow_three :
    order48_RM_G11_tau3 ^ 3 = 1 := by
  apply MulEquiv.ext
  rintro ⟨a, b⟩
  ext
  · change (order24_tau3Q8 ^ 3) a = a
    rw [order24_tau3Q8_pow_three]
    rfl
  · rfl

noncomputable def order48_RM_G11_action :
    Multiplicative (ZMod 3) →* MulAut order16_wild_G11 :=
  MonoidHom.mk' (fun x => order48_RM_G11_tau3 ^
    (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add order48_RM_G11_tau3_pow_three a.toAdd b.toAdd)

noncomputable instance order48_RM_G11_action_fintype :
    Fintype (SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) order48_RM_G11_action) :=
  Fintype.ofEquiv (order16_wild_G11 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

theorem order48_RM_G11_action_card_cube_roots :
    Nat.card {x : SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) order48_RM_G11_action // x ^ 3 = 1} = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem order48_RM_G11_action_card_sylow_three :
    Nat.card (Sylow 3 (SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) order48_RM_G11_action)) = 4 :=
  (order48_c3_action_card_sylow_three_eq_four_iff
    (card_order16_wild_G11) order48_RM_G11_action).mpr
    order48_RM_G11_action_card_cube_roots

noncomputable def order48_RM_G11_splitEquiv :
    SemidirectProduct order16_wild_G11
        (Multiplicative (ZMod 3)) order48_RM_G11_action ≃*
      Multiplicative (ZMod 2) × order24_RN where
  toFun x := (x.left.2, ⟨x.left.1, x.right⟩)
  invFun x := ⟨(x.2.left, x.1), x.2.right⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, c⟩
    rfl
  right_inv := by
    rintro ⟨a, ⟨b, c⟩⟩
    rfl
  map_mul' := by
    rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
    ext <;> revert a b c a' b' c' <;> decide

theorem order48_RM_G11_action_mulEquiv_C2xRN :
    Nonempty (SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) order48_RM_G11_action ≃*
      Multiplicative (ZMod 2) × order24_RN) :=
  ⟨order48_RM_G11_splitEquiv⟩

theorem order48_RM_G11_action_mem_residualKnownReps :
    Nonempty (SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) order48_RM_G11_action ≃*
      order48_four_residualKnownReps 6) := by
  obtain ⟨eSL⟩ := order24_SL23_mulEquiv_RN
  exact ⟨order48_RM_G11_splitEquiv.trans
    (MulEquiv.prodCongr (MulEquiv.refl _) eSL.symm)⟩

/-! ### The `G₁₀` order-three orbit representative -/

private noncomputable def order48_RM_G10_tauFun (x : order16_wild_G10) :
    order16_wild_G10 :=
  let a := SemidirectProduct.inl
      ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 2)) *
      SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))
  let b := SemidirectProduct.inl
      ((Multiplicative.ofAdd (3 : ZMod 4)),
        (1 : Multiplicative (ZMod 2))) *
      SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))
  let c := SemidirectProduct.inl
      ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 2))
  a ^ (Multiplicative.toAdd x.left.1).val *
    b ^ (Multiplicative.toAdd x.left.2).val *
    c ^ (Multiplicative.toAdd x.right).val

noncomputable def order48_RM_G10_tau3 : MulAut order16_wild_G10 where
  toFun := order48_RM_G10_tauFun
  invFun x := order48_RM_G10_tauFun (order48_RM_G10_tauFun x)
  left_inv := by
    intro x
    change order48_RM_G10_tauFun
      (order48_RM_G10_tauFun (order48_RM_G10_tauFun x)) = x
    revert x
    decide
  right_inv := by
    intro x
    change order48_RM_G10_tauFun
      (order48_RM_G10_tauFun (order48_RM_G10_tauFun x)) = x
    revert x
    decide
  map_mul' := by
    intro x y
    revert x y
    decide

set_option maxHeartbeats 1600000 in
-- The explicit `G₁₀` coordinate calculation unfolds three finite products.
theorem order48_RM_G10_tau3_pow_three :
    order48_RM_G10_tau3 ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  revert x
  decide +kernel

noncomputable def order48_RM_G10_action :
    Multiplicative (ZMod 3) →* MulAut order16_wild_G10 :=
  MonoidHom.mk' (fun x => order48_RM_G10_tau3 ^
    (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add order48_RM_G10_tau3_pow_three a.toAdd b.toAdd)

noncomputable instance order48_RM_G10_action_fintype :
    Fintype (SemidirectProduct order16_wild_G10
      (Multiplicative (ZMod 3)) order48_RM_G10_action) :=
  Fintype.ofEquiv (order16_wild_G10 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

theorem order48_RM_G10_action_card_cube_roots :
    Nat.card {x : SemidirectProduct order16_wild_G10
      (Multiplicative (ZMod 3)) order48_RM_G10_action // x ^ 3 = 1} = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem order48_RM_G10_action_card_sylow_three :
    Nat.card (Sylow 3 (SemidirectProduct order16_wild_G10
      (Multiplicative (ZMod 3)) order48_RM_G10_action)) = 4 :=
  (order48_c3_action_card_sylow_three_eq_four_iff
    (card_order16_wild_G10) order48_RM_G10_action).mpr
    order48_RM_G10_action_card_cube_roots

/-! ### The `G₈` automorphism filter -/

private noncomputable def order48_RM_G8_r : order16_wild_G8 :=
  SemidirectProduct.inl
    (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 2)))

private noncomputable def order48_RM_G8_s : order16_wild_G8 :=
  SemidirectProduct.inl
    ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 2))

private noncomputable def order48_RM_G8_t : order16_wild_G8 :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

private theorem order48_RM_G8_hom_eval
    {M : Type*} [Monoid M] (f : order16_wild_G8 →* M)
    (x : order16_wild_G8) :
    f x = f order48_RM_G8_r ^ (Multiplicative.toAdd x.left.1).val *
      f order48_RM_G8_s ^ (Multiplicative.toAdd x.left.2).val *
      f order48_RM_G8_t ^ (Multiplicative.toAdd x.right).val := by
  have hx : x = order48_RM_G8_r ^ (Multiplicative.toAdd x.left.1).val *
      order48_RM_G8_s ^ (Multiplicative.toAdd x.left.2).val *
      order48_RM_G8_t ^ (Multiplicative.toAdd x.right).val := by
    revert x
    decide
  calc
    f x = f (order48_RM_G8_r ^ (Multiplicative.toAdd x.left.1).val *
        order48_RM_G8_s ^ (Multiplicative.toAdd x.left.2).val *
        order48_RM_G8_t ^ (Multiplicative.toAdd x.right).val) := congrArg f hx
    _ = f order48_RM_G8_r ^ (Multiplicative.toAdd x.left.1).val *
        f order48_RM_G8_s ^ (Multiplicative.toAdd x.left.2).val *
        f order48_RM_G8_t ^ (Multiplicative.toAdd x.right).val := by
      rw [map_mul, map_mul, map_pow, map_pow, map_pow]

/-! ### The elementary-abelian RM kernel `G₀` -/

noncomputable def order48_RM_G0_tau3 : MulAut order16_wild_C2pow4 where
  toFun p := (p.2.1, p.1 * p.2.1, p.2.2.1, p.2.2.2)
  invFun p := (p.1 * p.2.1, p.1, p.2.2.1, p.2.2.2)
  left_inv := by
    rintro ⟨a, b, c, d⟩
    ext <;> revert a b c d <;> decide
  right_inv := by
    rintro ⟨a, b, c, d⟩
    ext <;> revert a b c d <;> decide
  map_mul' := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩
    ext <;> revert a b c d a' b' c' d' <;> decide

theorem order48_RM_G0_tau3_pow_three :
    order48_RM_G0_tau3 ^ 3 = 1 := by
  apply MulEquiv.ext
  rintro ⟨a, b, c, d⟩
  revert a b c d
  decide

noncomputable def order48_RM_G0_action :
    Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4 :=
  MonoidHom.mk' (fun x => order48_RM_G0_tau3 ^
    (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add order48_RM_G0_tau3_pow_three a.toAdd b.toAdd)

noncomputable instance order48_RM_G0_action_fintype :
    Fintype (SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) order48_RM_G0_action) :=
  Fintype.ofEquiv (order16_wild_C2pow4 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

theorem order48_RM_G0_action_card_cube_roots :
    Nat.card {x : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) order48_RM_G0_action // x ^ 3 = 1} = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem order48_RM_G0_action_card_sylow_three :
    Nat.card (Sylow 3 (SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) order48_RM_G0_action)) = 4 :=
  (order48_c3_action_card_sylow_three_eq_four_iff
    (by rw [Nat.card_eq_fintype_card]; decide) order48_RM_G0_action).mpr
    order48_RM_G0_action_card_cube_roots

/-- Any elementary-abelian residual action has a four-element fixed subgroup.
This is the structural input for the remaining `G₀` orbit calculation. -/
theorem order48_RM_G0_fixed_card_four
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hRoots : Nat.card {x : SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ // x ^ 3 = 1} = 9) :
    Nat.card {x : order16_wild_C2pow4 //
      φ order48_c3Generator x = x} = 4 := by
  apply order48_c3_action_fixed_card_four_of_card_cube_roots_nine
    (by rw [Nat.card_eq_fintype_card]; decide)
    (fun x => by revert x; decide) φ hRoots

noncomputable def order48_RM_G0_splitEquiv :
    SemidirectProduct order16_wild_C2pow4
        (Multiplicative (ZMod 3)) order48_RM_G0_action ≃*
      ElemAbelianRep 2 × SemidirectProduct order48_RM_E4
        (Multiplicative (ZMod 3)) order48_RM_E4_action where
  toFun x := ((x.left.2.2.1, x.left.2.2.2),
    ⟨(x.left.1, x.left.2.1), x.right⟩)
  invFun x := ⟨(x.2.left.1, x.2.left.2, x.1.1, x.1.2), x.2.right⟩
  left_inv := by
    rintro ⟨⟨a, b, c, d⟩, e⟩
    rfl
  right_inv := by
    rintro ⟨⟨c, d⟩, ⟨⟨a, b⟩, e⟩⟩
    rfl
  map_mul' := by
    rintro ⟨⟨a, b, c, d⟩, e⟩ ⟨⟨a', b', c', d'⟩, e'⟩
    ext <;> revert a b c d e a' b' c' d' e' <;> decide

theorem order48_RM_G0_action_mulEquiv_V4xA4 :
    Nonempty (SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) order48_RM_G0_action ≃*
      order48_four_V4xA4) := by
  have hcard : Nat.card (SemidirectProduct order48_RM_E4
      (Multiplicative (ZMod 3)) order48_RM_E4_action) = 12 := by
    rw [SemidirectProduct.card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    decide
  have hroots : Nat.card {x : SemidirectProduct order48_RM_E4
      (Multiplicative (ZMod 3)) order48_RM_E4_action // x ^ 3 = 1} = 9 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hsyl := order48_card_sylow_three_eq_four_of_card_pow_three_eq_one
    hcard hroots
  obtain ⟨eA⟩ := fourP_12_equiv_A4_of_card_sylow_three_eq_four hcard hsyl
  exact ⟨order48_RM_G0_splitEquiv.trans
    (MulEquiv.prodCongr (MulEquiv.refl _) eA)⟩

theorem order48_RM_G0_action_mem_residualKnownReps :
    Nonempty (SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) order48_RM_G0_action ≃*
      order48_four_residualKnownReps 5) := by
  simpa using order48_RM_G0_action_mulEquiv_V4xA4

/-! ### Orbit-to-residual bridges -/

theorem order48_RM_G7_mem_residual_of_conj
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G7)
    (θ : MulAut order16_wild_G7)
    (hθ : (MulAut.conj θ).toMonoidHom.comp φ = order48_RM_G7_action) :
    ∃ j : Fin 8, Nonempty (SemidirectProduct order16_wild_G7
      (Multiplicative (ZMod 3)) φ ≃* order48_four_residualKnownReps j) := by
  refine ⟨3, ?_⟩
  obtain ⟨eφ⟩ := order48_c3_action_conj_orbit_move θ hθ
  obtain ⟨eR⟩ := order48_RM_G7_action_mem_residualKnownReps
  exact ⟨eφ.trans eR⟩

theorem order48_RM_G0_mem_residual_of_conj
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (θ : MulAut order16_wild_C2pow4)
    (hθ : (MulAut.conj θ).toMonoidHom.comp φ = order48_RM_G0_action) :
    ∃ j : Fin 8, Nonempty (SemidirectProduct order16_wild_C2pow4
      (Multiplicative (ZMod 3)) φ ≃* order48_four_residualKnownReps j) := by
  refine ⟨5, ?_⟩
  obtain ⟨eφ⟩ := order48_c3_action_conj_orbit_move θ hθ
  obtain ⟨eR⟩ := order48_RM_G0_action_mem_residualKnownReps
  exact ⟨eφ.trans eR⟩

theorem order48_RM_G11_mem_residual_of_conj
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G11)
    (θ : MulAut order16_wild_G11)
    (hθ : (MulAut.conj θ).toMonoidHom.comp φ = order48_RM_G11_action) :
    ∃ j : Fin 8, Nonempty (SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) φ ≃* order48_four_residualKnownReps j) := by
  refine ⟨6, ?_⟩
  obtain ⟨eφ⟩ := order48_c3_action_conj_orbit_move θ hθ
  obtain ⟨eR⟩ := order48_RM_G11_action_mem_residualKnownReps
  exact ⟨eφ.trans eR⟩

end Smallgroups.UsefulTheorems
