/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.P9xH8_E8

/-!
# Groups of order 72: the `E9 ⋊ Q8` cell

This file classifies the semidirect products `E9 ⋊[φ] Q8` with
`Q8 = QuaternionGroup 2`.  A homomorphism `φ : Q8 → MulAut (ElemAbelianRep 3) ≅ GL(2,3)`
is determined by `Fi = φ(i)`, `Fj = φ(j)` with `Fi⁴ = 1`, `Fj² = Fi²`, `Fj·Fi = Fi³·Fj`.
The `2`-subgroups of `GL(2,3)` that are quotients of `Q8` are `{1}`, `C2`, `V4` and `Q8`
(the last unique), and up to `Aut(Q8) × GL(2,3)`-conjugacy there are exactly **four**
nontrivial orbits (matching the GAP census groups `#24, 26, 31, 41` of order `72` with
normal `C3²` and quaternion Sylow-`2`):

* `order72_E9_Q8_negI`: `C2`-image `{1, -I}` (GAP `#31`);
* `order72_E9_Q8_reflectI`: `C2`-image a reflection subgroup (GAP `#26`);
* `order72_E9_Q8_v4`: `V4`-image (GAP `#24`);
* `order72_E9_Q8_faithful`: the faithful `Q8`-action (GAP `#41` `= PSU(3,2)`).

The classification theorem is `order72_e9_q8_semidirect_cases`.  The concrete actions
are built by generator values with the `64`-point multiplicativity check done by
`order72_E9_aut_ext` and `decide`; the `Aut(Q8)` moves are built likewise with plain
`decide` over the (tiny) quaternion group.
-/

namespace Smallgroups.UsefulTheorems

open P3Group QuaternionGroup

/-! ### Generators of `Q8` and homomorphism extensionality. -/

/-- The generator `i` of `Q8`. -/
def qi : QuaternionGroup 2 := .a 1

/-- The generator `j` of `Q8`. -/
def qj : QuaternionGroup 2 := .xa 0

theorem qi_pow4 : qi ^ 4 = 1 := by decide
theorem qj_sq_eq_qi_sq : qj ^ 2 = qi ^ 2 := by decide
theorem qj_mul_qi : qj * qi = qi ^ 3 * qj := by decide

/-- The eight elements of `Q8` as monomials in `i, j`. -/
theorem q8gen : ∀ x : QuaternionGroup 2, x = 1 ∨ x = qi ∨ x = qi ^ 2 ∨ x = qi ^ 3 ∨
    x = qj ∨ x = qj * qi ∨ x = qj * qi ^ 2 ∨ x = qj * qi ^ 3 := by
  decide

/-- Homomorphisms out of `Q8` are determined by the two generators. -/
theorem q8_hom_ext {M : Type*} [Group M] {φ ψ : QuaternionGroup 2 →* M}
    (h1 : φ qi = ψ qi) (h2 : φ qj = ψ qj) : φ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases q8gen x with h | h | h | h | h | h | h | h <;> subst h <;>
    simp [map_mul, map_pow, map_one, h1, h2]

/-- The map `Q8 → A` sending `iᵏ ↦ Fiᵏ`, `j·iᵏ ↦ Fj·Fiᵏ`. -/
def order72_Q8_mapOfValues {A : Type*} [Group A] (Fi Fj : A) : QuaternionGroup 2 → A
  | .a k => Fi ^ k.val
  | .xa k => Fj * Fi ^ k.val

/-! ### The four standard actions of `Q8` on `C3 × C3`. -/

/-- The `C2`-action with `i ↦ -I`, `j ↦ 1`. -/
noncomputable abbrev order72_e9Q8NegIAction : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3) where
  toFun := order72_Q8_mapOfValues order72_E9_negAut 1
  map_one' := by
    change order72_E9_negAut ^ (0 : ZMod 4).val = 1
    simp
  map_mul' x y := by
    apply order72_E9_aut_ext <;> cases x <;> cases y <;> decide +revert

/-- The `C2`-action with `i ↦ reflection`, `j ↦ 1`. -/
noncomputable abbrev order72_e9Q8ReflectIAction :
    QuaternionGroup 2 →* MulAut (ElemAbelianRep 3) where
  toFun := order72_Q8_mapOfValues order72_E9_reflectAut 1
  map_one' := by
    change order72_E9_reflectAut ^ (0 : ZMod 4).val = 1
    simp
  map_mul' x y := by
    apply order72_E9_aut_ext <;> cases x <;> cases y <;> decide +revert

/-- The `V4`-action with `i ↦ -I`, `j ↦ reflection`. -/
noncomputable abbrev order72_e9Q8V4Action : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3) where
  toFun := order72_Q8_mapOfValues order72_E9_negAut order72_E9_reflectAut
  map_one' := by
    change order72_E9_negAut ^ (0 : ZMod 4).val = 1
    simp
  map_mul' x y := by
    apply order72_E9_aut_ext <;> cases x <;> cases y <;> decide +revert

/-- The faithful `Q8`-action with `i ↦` order-`4`, `j ↦` its shear-conjugate. -/
noncomputable abbrev order72_e9Q8FaithfulAction :
    QuaternionGroup 2 →* MulAut (ElemAbelianRep 3) where
  toFun := order72_Q8_mapOfValues order72_E9_order4Aut order72_E9_order4Shear
  map_one' := by
    change order72_E9_order4Aut ^ (0 : ZMod 4).val = 1
    simp
  map_mul' x y := by
    apply order72_E9_aut_ext <;> cases x <;> cases y <;> decide +revert

/-- The four nontrivial representatives of the `E9 ⋊ Q8` cell. -/
abbrev order72_E9_Q8_negI : Type :=
  SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) order72_e9Q8NegIAction

abbrev order72_E9_Q8_reflectI : Type :=
  SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) order72_e9Q8ReflectIAction

abbrev order72_E9_Q8_v4 : Type :=
  SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) order72_e9Q8V4Action

abbrev order72_E9_Q8_faithful : Type :=
  SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) order72_e9Q8FaithfulAction

/-! ### `Aut(Q8)` moves used in the classification. -/

/-- The automorphism of `Q8` swapping `i ↔ j`. -/
noncomputable def order72_Q8_swapIJ : QuaternionGroup 2 ≃* QuaternionGroup 2 where
  toFun := order72_Q8_mapOfValues qj qi
  invFun := order72_Q8_mapOfValues qj qi
  left_inv x := by decide +revert
  right_inv x := by decide +revert
  map_mul' x y := by decide +revert

/-- The automorphism of `Q8` shearing `i ↦ i`, `j ↦ i·j`. -/
noncomputable def order72_Q8_shearIJ : QuaternionGroup 2 ≃* QuaternionGroup 2 where
  toFun := order72_Q8_mapOfValues qi (qi * qj)
  invFun := order72_Q8_mapOfValues qi (qi ^ 3 * qj)
  left_inv x := by decide +revert
  right_inv x := by decide +revert
  map_mul' x y := by decide +revert

/-! ### Value lemmas for the standard actions and the moves. -/

@[simp] theorem order72_e9Q8NegIAction_qi : order72_e9Q8NegIAction qi = order72_E9_negAut := by
  change order72_E9_negAut ^ (1 : ZMod 4).val = order72_E9_negAut
  rw [show (1 : ZMod 4).val = 1 from by decide, pow_one]

@[simp] theorem order72_e9Q8NegIAction_qj : order72_e9Q8NegIAction qj = 1 := by
  change 1 * order72_E9_negAut ^ (0 : ZMod 4).val = 1
  simp

@[simp] theorem order72_e9Q8ReflectIAction_qi :
    order72_e9Q8ReflectIAction qi = order72_E9_reflectAut := by
  change order72_E9_reflectAut ^ (1 : ZMod 4).val = order72_E9_reflectAut
  rw [show (1 : ZMod 4).val = 1 from by decide, pow_one]

@[simp] theorem order72_e9Q8ReflectIAction_qj : order72_e9Q8ReflectIAction qj = 1 := by
  change 1 * order72_E9_reflectAut ^ (0 : ZMod 4).val = 1
  simp

@[simp] theorem order72_e9Q8V4Action_qi : order72_e9Q8V4Action qi = order72_E9_negAut := by
  change order72_E9_negAut ^ (1 : ZMod 4).val = order72_E9_negAut
  rw [show (1 : ZMod 4).val = 1 from by decide, pow_one]

@[simp] theorem order72_e9Q8V4Action_qj :
    order72_e9Q8V4Action qj = order72_E9_reflectAut := by
  change order72_E9_reflectAut * order72_E9_negAut ^ (0 : ZMod 4).val = order72_E9_reflectAut
  simp

@[simp] theorem order72_e9Q8FaithfulAction_qi :
    order72_e9Q8FaithfulAction qi = order72_E9_order4Aut := by
  change order72_E9_order4Aut ^ (1 : ZMod 4).val = order72_E9_order4Aut
  rw [show (1 : ZMod 4).val = 1 from by decide, pow_one]

@[simp] theorem order72_e9Q8FaithfulAction_qj :
    order72_e9Q8FaithfulAction qj = order72_E9_order4Shear := by
  change order72_E9_order4Shear * order72_E9_order4Aut ^ (0 : ZMod 4).val =
    order72_E9_order4Shear
  simp

@[simp] theorem order72_Q8_swapIJ_qi : order72_Q8_swapIJ qi = qj := by decide
@[simp] theorem order72_Q8_swapIJ_qj : order72_Q8_swapIJ qj = qi := by decide
@[simp] theorem order72_Q8_shearIJ_qi : order72_Q8_shearIJ qi = qi := by decide
@[simp] theorem order72_Q8_shearIJ_qj : order72_Q8_shearIJ qj = qi * qj := by decide

@[simp] theorem order72_Q8_shearIJ_pow2_qi : (order72_Q8_shearIJ ^ 2) qi = qi := by decide
@[simp] theorem order72_Q8_shearIJ_pow2_qj :
    (order72_Q8_shearIJ ^ 2) qj = qi ^ 2 * qj := by decide
@[simp] theorem order72_Q8_shearIJ_pow3_qi : (order72_Q8_shearIJ ^ 3) qi = qi := by decide
@[simp] theorem order72_Q8_shearIJ_pow3_qj :
    (order72_Q8_shearIJ ^ 3) qj = qi ^ 3 * qj := by decide

/-! ### The classification of `Q8`-actions on `C3 × C3`. -/

/-- **The `E9 ⋊ Q8` cell**: every action `φ : Q8 → MulAut (C3 × C3)` gives a semidirect
product isomorphic to the direct product or to one of the four nontrivial
representatives.  The proof cases on `Fi = φ(i)` via `order72_E9_pow4_cases`; the
relation `Fj² = Fi²` feeds `order72_E9_sq_cases` (or the centralizer refinements after
transporting `Fi` to a standard element), and the faithful case uses the quaternion
partner classification `order72_E9_order4_q8_partner_cases`. -/
theorem order72_e9_q8_semidirect_cases (φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3)) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ ≃*
      ElemAbelianRep 3 × QuaternionGroup 2) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ ≃*
      order72_E9_Q8_negI) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ ≃*
      order72_E9_Q8_reflectI) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ ≃*
      order72_E9_Q8_v4) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ ≃*
      order72_E9_Q8_faithful) := by
  have hFi4 : (φ qi) ^ 4 = 1 := by rw [← map_pow, qi_pow4, map_one]
  have hFj2 : (φ qj) ^ 2 = (φ qi) ^ 2 := by rw [← map_pow, ← map_pow, qj_sq_eq_qi_sq]
  have hcomm : φ qj * φ qi = (φ qi) ^ 3 * φ qj := by
    rw [← map_mul, qj_mul_qi, map_mul, map_pow]
  rcases order72_E9_pow4_cases (φ qi) hFi4 with hF | hF | ⟨θ, hF⟩ | ⟨θ, hF⟩
  · -- `Fi = 1`: the action factors through the `C2` quotient `Q8/<i>`.
    have hFj21 : (φ qj) ^ 2 = 1 := by rw [hFj2, hF, one_pow]
    rcases order72_E9_sq_cases (φ qj) hFj21 with hG | hG | ⟨θ', hG⟩
    · left
      have hφ : φ = 1 := by apply q8_hom_ext <;> simp [hF, hG]
      exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
    · -- `Fj = -I`: precompose the swap `i ↔ j` of the `negI` action.
      right
      left
      have hφ : φ = order72_e9Q8NegIAction.comp order72_Q8_swapIJ.toMonoidHom := by
        apply q8_hom_ext
        · change φ qi = order72_e9Q8NegIAction (order72_Q8_swapIJ qi)
          rw [hF]
          simp
        · change φ qj = order72_e9Q8NegIAction (order72_Q8_swapIJ qj)
          rw [hG]
          simp
      exact ⟨(semidirectProductCongr_eq hφ).trans
        (semidirectProductCongrAut (φ := order72_e9Q8NegIAction) order72_Q8_swapIJ)⟩
    · -- `Fj` conjugate to the reflection: transport, then swap to `reflectI`.
      right
      right
      left
      have hφ : (MulAut.conj θ').toMonoidHom.comp φ =
          order72_e9Q8ReflectIAction.comp order72_Q8_swapIJ.toMonoidHom := by
        apply q8_hom_ext
        · change (MulAut.conj θ') (φ qi) =
            order72_e9Q8ReflectIAction (order72_Q8_swapIJ qi)
          rw [hF, map_one]
          simp
        · change (MulAut.conj θ') (φ qj) =
            order72_e9Q8ReflectIAction (order72_Q8_swapIJ qj)
          rw [hG]
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ').trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9Q8ReflectIAction)
            order72_Q8_swapIJ))⟩
  · -- `Fi = -I`.
    have hFj21 : (φ qj) ^ 2 = 1 := by rw [hFj2, hF, order72_E9_negAut_sq]
    rcases order72_E9_sq_cases (φ qj) hFj21 with hG | hG | ⟨θ', hG⟩
    · -- `Fj = 1`: the `negI` action itself.
      right
      left
      have hφ : φ = order72_e9Q8NegIAction := by apply q8_hom_ext <;> simp [hF, hG]
      exact ⟨semidirectProductCongr_eq hφ⟩
    · -- `Fj = -I`: precompose the shear `j ↦ i·j` of the `negI` action.
      right
      left
      have hφ : φ = order72_e9Q8NegIAction.comp order72_Q8_shearIJ.toMonoidHom := by
        apply q8_hom_ext
        · change φ qi = order72_e9Q8NegIAction (order72_Q8_shearIJ qi)
          rw [hF]
          simp
        · change φ qj = order72_e9Q8NegIAction (order72_Q8_shearIJ qj)
          rw [hG]
          simp [map_mul]
      exact ⟨(semidirectProductCongr_eq hφ).trans
        (semidirectProductCongrAut (φ := order72_e9Q8NegIAction) order72_Q8_shearIJ)⟩
    · -- `Fj` conjugate to the reflection: transport gives the `V4` action.
      right
      right
      right
      left
      have hφ : (MulAut.conj θ').toMonoidHom.comp φ = order72_e9Q8V4Action := by
        apply q8_hom_ext
        · change (MulAut.conj θ') (φ qi) = order72_e9Q8V4Action qi
          rw [hF, order72_E9_conj_negAut]
          simp
        · change (MulAut.conj θ') (φ qj) = order72_e9Q8V4Action qj
          rw [hG]
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ').trans (semidirectProductCongr_eq hφ)⟩
  · -- `Fi` conjugate to the standard reflection; transport and case on `Fj'`.
    have hFj'2 : ((MulAut.conj θ) (φ qj)) ^ 2 = 1 := by
      rw [← map_pow, hFj2, map_pow, hF, order72_E9_reflectAut_sq]
    have hr3 : order72_E9_reflectAut ^ 3 = order72_E9_reflectAut := by
      rw [pow_succ, order72_E9_reflectAut_sq, one_mul]
    have hcomm' : Commute ((MulAut.conj θ) (φ qj)) order72_E9_reflectAut := by
      have h3 := congrArg (MulAut.conj θ) hcomm
      rwa [map_mul, map_mul, map_pow, hF, hr3] at h3
    rcases order72_E9_reflect_centralizer_sq_cases ((MulAut.conj θ) (φ qj)) hFj'2 hcomm'
      with hG' | hG' | hG' | hG'
    · -- `Fj' = 1`: the `reflectI` action.
      right
      right
      left
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ = order72_e9Q8ReflectIAction := by
        apply q8_hom_ext
        · change (MulAut.conj θ) (φ qi) = _
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ qj) = _
          rw [hG']
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans (semidirectProductCongr_eq hφ)⟩
    · -- `Fj' = -I`: the `V4` action precomposed with the swap `i ↔ j`.
      right
      right
      right
      left
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9Q8V4Action.comp order72_Q8_swapIJ.toMonoidHom := by
        apply q8_hom_ext
        · change (MulAut.conj θ) (φ qi) = order72_e9Q8V4Action (order72_Q8_swapIJ qi)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ qj) = order72_e9Q8V4Action (order72_Q8_swapIJ qj)
          rw [hG']
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9Q8V4Action) order72_Q8_swapIJ))⟩
    · -- `Fj' = reflect`: the `reflectI` action precomposed with the shear `j ↦ i·j`.
      right
      right
      left
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9Q8ReflectIAction.comp order72_Q8_shearIJ.toMonoidHom := by
        apply q8_hom_ext
        · change (MulAut.conj θ) (φ qi) =
            order72_e9Q8ReflectIAction (order72_Q8_shearIJ qi)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ qj) =
            order72_e9Q8ReflectIAction (order72_Q8_shearIJ qj)
          rw [hG']
          simp [map_mul]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9Q8ReflectIAction)
            order72_Q8_shearIJ))⟩
    · -- `Fj' = diag(1,-1)`: the `V4` action precomposed with shear-then-swap.
      right
      right
      right
      left
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9Q8V4Action.comp
            (order72_Q8_shearIJ.trans order72_Q8_swapIJ).toMonoidHom := by
        apply q8_hom_ext
        · change (MulAut.conj θ) (φ qi) =
            order72_e9Q8V4Action ((order72_Q8_shearIJ.trans order72_Q8_swapIJ) qi)
          rw [hF]
          simp [MulEquiv.trans_apply]
        · change (MulAut.conj θ) (φ qj) =
            order72_e9Q8V4Action ((order72_Q8_shearIJ.trans order72_Q8_swapIJ) qj)
          rw [hG']
          simp [MulEquiv.trans_apply, map_mul, order72_E9_reflectAut_mul_negAut]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9Q8V4Action)
            (order72_Q8_shearIJ.trans order72_Q8_swapIJ)))⟩
  · -- `Fi` conjugate to the standard order-`4` element; transport and case on `Fj'`.
    have hFj'2 : ((MulAut.conj θ) (φ qj)) ^ 2 = order72_E9_negAut := by
      rw [← map_pow, hFj2, map_pow, hF, order72_E9_order4Aut_sq]
    have hconj' : (MulAut.conj θ) (φ qj) * order72_E9_order4Aut =
        order72_E9_order4Aut ^ 3 * (MulAut.conj θ) (φ qj) := by
      have h3 := congrArg (MulAut.conj θ) hcomm
      rwa [map_mul, map_mul, map_pow, hF] at h3
    rcases order72_E9_order4_q8_partner_cases ((MulAut.conj θ) (φ qj)) hFj'2 hconj'
      with hG' | hG' | hG' | hG'
    · -- `Fj' = S`: the faithful action.
      right
      right
      right
      right
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ = order72_e9Q8FaithfulAction := by
        apply q8_hom_ext
        · change (MulAut.conj θ) (φ qi) = _
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ qj) = _
          rw [hG']
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans (semidirectProductCongr_eq hφ)⟩
    · -- `Fj' = R·S`: the faithful action precomposed with the shear `j ↦ i·j`.
      right
      right
      right
      right
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9Q8FaithfulAction.comp order72_Q8_shearIJ.toMonoidHom := by
        apply q8_hom_ext
        · change (MulAut.conj θ) (φ qi) = order72_e9Q8FaithfulAction (order72_Q8_shearIJ qi)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ qj) = order72_e9Q8FaithfulAction (order72_Q8_shearIJ qj)
          rw [hG']
          simp [map_mul]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9Q8FaithfulAction)
            order72_Q8_shearIJ))⟩
    · -- `Fj' = R²·S`: the faithful action precomposed with the squared shear.
      right
      right
      right
      right
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9Q8FaithfulAction.comp (order72_Q8_shearIJ ^ 2).toMonoidHom := by
        apply q8_hom_ext
        · change (MulAut.conj θ) (φ qi) =
            order72_e9Q8FaithfulAction ((order72_Q8_shearIJ ^ 2) qi)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ qj) =
            order72_e9Q8FaithfulAction ((order72_Q8_shearIJ ^ 2) qj)
          rw [hG']
          simp [map_mul, map_pow]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9Q8FaithfulAction)
            (order72_Q8_shearIJ ^ 2)))⟩
    · -- `Fj' = R³·S`: the faithful action precomposed with the cubed shear.
      right
      right
      right
      right
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9Q8FaithfulAction.comp (order72_Q8_shearIJ ^ 3).toMonoidHom := by
        apply q8_hom_ext
        · change (MulAut.conj θ) (φ qi) =
            order72_e9Q8FaithfulAction ((order72_Q8_shearIJ ^ 3) qi)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ qj) =
            order72_e9Q8FaithfulAction ((order72_Q8_shearIJ ^ 3) qj)
          rw [hG']
          simp [map_mul, map_pow]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9Q8FaithfulAction)
            (order72_Q8_shearIJ ^ 3)))⟩

/-- The `G`-level version of the `E9 ⋊ Q8` classification. -/
theorem order72_e9_q8_branch_cases {G : Type*} [Group G]
    {φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ) :
    Nonempty (G ≃* ElemAbelianRep 3 × QuaternionGroup 2) ∨
    Nonempty (G ≃* order72_E9_Q8_negI) ∨
    Nonempty (G ≃* order72_E9_Q8_reflectI) ∨
    Nonempty (G ≃* order72_E9_Q8_v4) ∨
    Nonempty (G ≃* order72_E9_Q8_faithful) := by
  rcases order72_e9_q8_semidirect_cases φ with h | h | h | h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inl ⟨e.trans eh⟩)
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩)))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans eh⟩)))

/-! ### The Sylow-`3`-normal branch with only the `E9 ⋊ D4` cell remaining. -/

/-- The fully classified part of the Sylow-`3`-normal branch after solving the
`E9 ⋊ Q8` cell: the previous solved cases together with the direct product and the
four `E9 ⋊ Q8` representatives. -/
abbrev order72Sylow3NormalSolvedC9AllE9C8H2E8Q8Cases (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9AllE9C8H2E8Cases G ∨
    Nonempty (G ≃* ElemAbelianRep 3 × QuaternionGroup 2) ∨
      Nonempty (G ≃* order72_E9_Q8_negI) ∨
        Nonempty (G ≃* order72_E9_Q8_reflectI) ∨
          Nonempty (G ≃* order72_E9_Q8_v4) ∨
            Nonempty (G ≃* order72_E9_Q8_faithful)

/-- The remaining action problem of the Sylow-`3`-normal branch: `E9 ⋊ D4`. -/
abbrev order72Sylow3NormalRemainingSemidirectCasesE9D4 (G : Type*) [Group G] : Prop :=
  ∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
    Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)

/-- The Sylow-`3`-normal branch with all cells but `E9 ⋊ D4` fully classified. -/
abbrev order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Q8Done (G : Type*) [Group G] :
    Prop :=
  order72Sylow3NormalSolvedC9AllE9C8H2E8Q8Cases G ∨
    order72Sylow3NormalRemainingSemidirectCasesE9D4 G

private theorem order72PartialC9AllE9C8H2E8Q8Done_of_e8_done {G : Type*} [Group G] :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Done G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Q8Done G := by
  intro hcases
  rcases hcases with hsolved | hrem
  · exact Or.inl (Or.inl hsolved)
  · rcases hrem with hD4 | hQ8
    · exact Or.inr hD4
    · obtain ⟨φ, ⟨e⟩⟩ := hQ8
      rcases order72_e9_q8_branch_cases e with h0 | h1 | h2 | h3 | h4
      · exact Or.inl (Or.inr (Or.inl h0))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h1)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h2))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h4)))))

theorem order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_h2_e8_q8_done
    {G : Type*} [Group G] :
    order72Sylow3NormalSemidirectCases G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Q8Done G := by
  intro hcases
  exact order72PartialC9AllE9C8H2E8Q8Done_of_e8_done
    (order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_h2_e8_done hcases)

/-- The `n₃ = 1` branch with all `C9 ⋊ H`, `E9 ⋊ C8`, `E9 ⋊ H2`, `E9 ⋊ E8` and
`E9 ⋊ Q8` cases reduced to explicit representatives. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_h2_e8_q8_done_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Q8Done G :=
  order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_h2_e8_q8_done
    (order72_semidirectProduct_standard_cases_of_sylow_three_normal hG hSyl)

/-- The `n₃ = 1` branch with all `C9 ⋊ H`, `E9 ⋊ C8`, `E9 ⋊ H2`, `E9 ⋊ E8` and
`E9 ⋊ Q8` cases reduced to explicit representatives. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_h2_e8_q8_done_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Q8Done G := by
  exact order72_partial_rep_cases_c9_all_e9_c8_h2_e8_q8_done_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- Current top-level reduction: in the Sylow-`3`-normal branch every cell except
`E9 ⋊ D4` is now explicit. -/
theorem order72_partial_classification_refined_c9_all_e9_c8_h2_e8_q8_done
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Q8Done G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl
      (order72_partial_rep_cases_c9_all_e9_c8_h2_e8_q8_done_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)

end Smallgroups.UsefulTheorems
