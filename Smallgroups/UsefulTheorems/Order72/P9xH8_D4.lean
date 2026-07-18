/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.P9xH8_Q8

/-!
# Groups of order 72: the `E9 ⋊ D4` cell

This file classifies the semidirect products `E9 ⋊[φ] D4` with
`D4 = DihedralGroup 4`.  A homomorphism `φ : D4 → MulAut (ElemAbelianRep 3) ≅ GL(2,3)`
is determined by `Fr = φ(r)`, `Fs = φ(s)` with `Fr⁴ = 1`, `Fs² = 1`,
`Fs·Fr = Fr³·Fs`.  Up to `Aut(D4) × GL(2,3)`-conjugacy there are exactly **seven**
nontrivial orbits (matching the GAP census groups `#21, 22, 23, 30, 33, 35, 40` of
order `72` with normal `C3²` and dihedral Sylow-`2`):

* `order72_E9_D4_sNeg`: `C2`-image `{1, -I}`, `r ↦ 1` (GAP `#33`-type);
* `order72_E9_D4_sReflect`: `C2`-image a reflection, `r ↦ 1` (GAP `#23` `= C3 ⋊ D12`);
* `order72_E9_D4_rNeg`: `C2`-image `{1, -I}`, `s ↦ 1` (GAP `#35`-type);
* `order72_E9_D4_rReflect`: `C2`-image a reflection, `s ↦ 1`
  (GAP `#30` `= C3 × (C3 ⋊ D4)`);
* `order72_E9_D4_v4NegReflect`: `V4`-image, `r ↦ -I`, `s ↦` reflection;
* `order72_E9_D4_v4ReflectNeg`: `V4`-image, `r ↦` reflection, `s ↦ -I`;
* `order72_E9_D4_faithful`: the faithful `D4`-action (GAP `#40` `= S3 ≀ C2`).

The classification theorem is `order72_e9_d4_semidirect_cases`; together with the
previous cells this completes the classification of the whole Sylow-`3`-normal branch
(`order72_partial_classification_refined_all_e9_done`).  The only `Aut(D4)` move needed
is the shear `s ↦ s·r` (`order72_D4_shearSR`), whose powers cycle the four dihedral
partners of the faithful pair and merge the duplicated `C2`/`V4` pairs.
-/

namespace Smallgroups.UsefulTheorems

open P3Group DihedralGroup

/-! ### Generators of `D4` and homomorphism extensionality. -/

/-- The rotation generator `r` of `D4`. -/
def dr : DihedralGroup 4 := .r 1

/-- The reflection generator `s` of `D4`. -/
def ds : DihedralGroup 4 := .sr 0

theorem dr_pow4 : dr ^ 4 = 1 := by decide
theorem ds_sq : ds ^ 2 = 1 := by decide
theorem ds_mul_dr : ds * dr = dr ^ 3 * ds := by decide

/-- The eight elements of `D4` as monomials in `r, s`. -/
theorem order72_d4gen : ∀ x : DihedralGroup 4, x = 1 ∨ x = dr ∨ x = dr ^ 2 ∨ x = dr ^ 3 ∨
    x = ds ∨ x = ds * dr ∨ x = ds * dr ^ 2 ∨ x = ds * dr ^ 3 := by
  decide

/-- Homomorphisms out of `D4` are determined by the two generators. -/
theorem d4_hom_ext {M : Type*} [Group M] {φ ψ : DihedralGroup 4 →* M}
    (h1 : φ dr = ψ dr) (h2 : φ ds = ψ ds) : φ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases order72_d4gen x with h | h | h | h | h | h | h | h <;> subst h <;>
    simp [map_mul, map_pow, map_one, h1, h2]

/-- The map `D4 → A` sending `rᵏ ↦ Frᵏ`, `s·rᵏ ↦ Fs·Frᵏ`. -/
def order72_D4_mapOfValues {A : Type*} [Group A] (Fr Fs : A) : DihedralGroup 4 → A
  | .r k => Fr ^ k.val
  | .sr k => Fs * Fr ^ k.val

/-! ### The seven standard actions of `D4` on `C3 × C3`. -/

/-- The `C2`-action with `r ↦ 1`, `s ↦ -I`. -/
noncomputable abbrev order72_e9D4SNegAction : DihedralGroup 4 →* MulAut (ElemAbelianRep 3) where
  toFun := order72_D4_mapOfValues 1 order72_E9_negAut
  map_one' := by
    change (1 : MulAut (ElemAbelianRep 3)) ^ (0 : ZMod 4).val = 1
    simp
  map_mul' x y := by
    apply order72_E9_aut_ext <;> cases x <;> cases y <;> decide +revert

/-- The `C2`-action with `r ↦ 1`, `s ↦` reflection. -/
noncomputable abbrev order72_e9D4SReflectAction :
    DihedralGroup 4 →* MulAut (ElemAbelianRep 3) where
  toFun := order72_D4_mapOfValues 1 order72_E9_reflectAut
  map_one' := by
    change (1 : MulAut (ElemAbelianRep 3)) ^ (0 : ZMod 4).val = 1
    simp
  map_mul' x y := by
    apply order72_E9_aut_ext <;> cases x <;> cases y <;> decide +revert

/-- The `C2`-action with `r ↦ -I`, `s ↦ 1`. -/
noncomputable abbrev order72_e9D4RNegAction : DihedralGroup 4 →* MulAut (ElemAbelianRep 3) where
  toFun := order72_D4_mapOfValues order72_E9_negAut 1
  map_one' := by
    change order72_E9_negAut ^ (0 : ZMod 4).val = 1
    simp
  map_mul' x y := by
    apply order72_E9_aut_ext <;> cases x <;> cases y <;> decide +revert

/-- The `C2`-action with `r ↦` reflection, `s ↦ 1`. -/
noncomputable abbrev order72_e9D4RReflectAction :
    DihedralGroup 4 →* MulAut (ElemAbelianRep 3) where
  toFun := order72_D4_mapOfValues order72_E9_reflectAut 1
  map_one' := by
    change order72_E9_reflectAut ^ (0 : ZMod 4).val = 1
    simp
  map_mul' x y := by
    apply order72_E9_aut_ext <;> cases x <;> cases y <;> decide +revert

/-- The `V4`-action with `r ↦ -I`, `s ↦` reflection. -/
noncomputable abbrev order72_e9D4V4NegReflectAction :
    DihedralGroup 4 →* MulAut (ElemAbelianRep 3) where
  toFun := order72_D4_mapOfValues order72_E9_negAut order72_E9_reflectAut
  map_one' := by
    change order72_E9_negAut ^ (0 : ZMod 4).val = 1
    simp
  map_mul' x y := by
    apply order72_E9_aut_ext <;> cases x <;> cases y <;> decide +revert

/-- The `V4`-action with `r ↦` reflection, `s ↦ -I`. -/
noncomputable abbrev order72_e9D4V4ReflectNegAction :
    DihedralGroup 4 →* MulAut (ElemAbelianRep 3) where
  toFun := order72_D4_mapOfValues order72_E9_reflectAut order72_E9_negAut
  map_one' := by
    change order72_E9_reflectAut ^ (0 : ZMod 4).val = 1
    simp
  map_mul' x y := by
    apply order72_E9_aut_ext <;> cases x <;> cases y <;> decide +revert

/-- The faithful `D4`-action with `r ↦` order-`4`, `s ↦` reflection. -/
noncomputable abbrev order72_e9D4FaithfulAction :
    DihedralGroup 4 →* MulAut (ElemAbelianRep 3) where
  toFun := order72_D4_mapOfValues order72_E9_order4Aut order72_E9_reflectAut
  map_one' := by
    change order72_E9_order4Aut ^ (0 : ZMod 4).val = 1
    simp
  map_mul' x y := by
    apply order72_E9_aut_ext <;> cases x <;> cases y <;> decide +revert

/-- The seven nontrivial representatives of the `E9 ⋊ D4` cell. -/
abbrev order72_E9_D4_sNeg : Type :=
  SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) order72_e9D4SNegAction

abbrev order72_E9_D4_sReflect : Type :=
  SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) order72_e9D4SReflectAction

abbrev order72_E9_D4_rNeg : Type :=
  SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) order72_e9D4RNegAction

abbrev order72_E9_D4_rReflect : Type :=
  SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) order72_e9D4RReflectAction

abbrev order72_E9_D4_v4NegReflect : Type :=
  SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) order72_e9D4V4NegReflectAction

abbrev order72_E9_D4_v4ReflectNeg : Type :=
  SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) order72_e9D4V4ReflectNegAction

abbrev order72_E9_D4_faithful : Type :=
  SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) order72_e9D4FaithfulAction

/-! ### The `Aut(D4)` shear `s ↦ s·r` and value lemmas. -/

/-- The automorphism of `D4` shearing `r ↦ r`, `s ↦ s·r`. -/
noncomputable def order72_D4_shearSR : DihedralGroup 4 ≃* DihedralGroup 4 where
  toFun := order72_D4_mapOfValues dr (ds * dr)
  invFun := order72_D4_mapOfValues dr (ds * dr ^ 3)
  left_inv x := by decide +revert
  right_inv x := by decide +revert
  map_mul' x y := by decide +revert

@[simp] theorem order72_D4_shearSR_dr : order72_D4_shearSR dr = dr := by decide
@[simp] theorem order72_D4_shearSR_ds : order72_D4_shearSR ds = ds * dr := by decide
@[simp] theorem order72_D4_shearSR_pow2_dr : (order72_D4_shearSR ^ 2) dr = dr := by decide
@[simp] theorem order72_D4_shearSR_pow2_ds :
    (order72_D4_shearSR ^ 2) ds = ds * dr ^ 2 := by decide
@[simp] theorem order72_D4_shearSR_pow3_dr : (order72_D4_shearSR ^ 3) dr = dr := by decide
@[simp] theorem order72_D4_shearSR_pow3_ds :
    (order72_D4_shearSR ^ 3) ds = ds * dr ^ 3 := by decide

@[simp] theorem order72_e9D4SNegAction_dr : order72_e9D4SNegAction dr = 1 := by
  change (1 : MulAut (ElemAbelianRep 3)) ^ (1 : ZMod 4).val = 1
  simp

@[simp] theorem order72_e9D4SNegAction_ds : order72_e9D4SNegAction ds = order72_E9_negAut := by
  change order72_E9_negAut * (1 : MulAut (ElemAbelianRep 3)) ^ (0 : ZMod 4).val =
    order72_E9_negAut
  simp

@[simp] theorem order72_e9D4SReflectAction_dr : order72_e9D4SReflectAction dr = 1 := by
  change (1 : MulAut (ElemAbelianRep 3)) ^ (1 : ZMod 4).val = 1
  simp

@[simp] theorem order72_e9D4SReflectAction_ds :
    order72_e9D4SReflectAction ds = order72_E9_reflectAut := by
  change order72_E9_reflectAut * (1 : MulAut (ElemAbelianRep 3)) ^ (0 : ZMod 4).val =
    order72_E9_reflectAut
  simp

@[simp] theorem order72_e9D4RNegAction_dr : order72_e9D4RNegAction dr = order72_E9_negAut := by
  change order72_E9_negAut ^ (1 : ZMod 4).val = order72_E9_negAut
  rw [show (1 : ZMod 4).val = 1 from by decide, pow_one]

@[simp] theorem order72_e9D4RNegAction_ds : order72_e9D4RNegAction ds = 1 := by
  change 1 * order72_E9_negAut ^ (0 : ZMod 4).val = 1
  simp

@[simp] theorem order72_e9D4RReflectAction_dr :
    order72_e9D4RReflectAction dr = order72_E9_reflectAut := by
  change order72_E9_reflectAut ^ (1 : ZMod 4).val = order72_E9_reflectAut
  rw [show (1 : ZMod 4).val = 1 from by decide, pow_one]

@[simp] theorem order72_e9D4RReflectAction_ds : order72_e9D4RReflectAction ds = 1 := by
  change 1 * order72_E9_reflectAut ^ (0 : ZMod 4).val = 1
  simp

@[simp] theorem order72_e9D4V4NegReflectAction_dr :
    order72_e9D4V4NegReflectAction dr = order72_E9_negAut := by
  change order72_E9_negAut ^ (1 : ZMod 4).val = order72_E9_negAut
  rw [show (1 : ZMod 4).val = 1 from by decide, pow_one]

@[simp] theorem order72_e9D4V4NegReflectAction_ds :
    order72_e9D4V4NegReflectAction ds = order72_E9_reflectAut := by
  change order72_E9_reflectAut * order72_E9_negAut ^ (0 : ZMod 4).val =
    order72_E9_reflectAut
  simp

@[simp] theorem order72_e9D4V4ReflectNegAction_dr :
    order72_e9D4V4ReflectNegAction dr = order72_E9_reflectAut := by
  change order72_E9_reflectAut ^ (1 : ZMod 4).val = order72_E9_reflectAut
  rw [show (1 : ZMod 4).val = 1 from by decide, pow_one]

@[simp] theorem order72_e9D4V4ReflectNegAction_ds :
    order72_e9D4V4ReflectNegAction ds = order72_E9_negAut := by
  change order72_E9_negAut * order72_E9_reflectAut ^ (0 : ZMod 4).val = order72_E9_negAut
  simp

@[simp] theorem order72_e9D4FaithfulAction_dr :
    order72_e9D4FaithfulAction dr = order72_E9_order4Aut := by
  change order72_E9_order4Aut ^ (1 : ZMod 4).val = order72_E9_order4Aut
  rw [show (1 : ZMod 4).val = 1 from by decide, pow_one]

@[simp] theorem order72_e9D4FaithfulAction_ds :
    order72_e9D4FaithfulAction ds = order72_E9_reflectAut := by
  change order72_E9_reflectAut * order72_E9_order4Aut ^ (0 : ZMod 4).val =
    order72_E9_reflectAut
  simp

/-! ### The classification of `D4`-actions on `C3 × C3`. -/

/-- **The `E9 ⋊ D4` cell**: every action `φ : D4 → MulAut (C3 × C3)` gives a semidirect
product isomorphic to the direct product or to one of the seven nontrivial
representatives.  The proof cases on `Fr = φ(r)` via `order72_E9_pow4_cases`; the
involution `Fs` is classified by `order72_E9_sq_cases` (or the centralizer refinement
after transporting `Fr` to the standard reflection, or the dihedral partner
classification `order72_E9_order4_d4_partner_cases` in the faithful case). -/
theorem order72_e9_d4_semidirect_cases (φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3)) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ ≃*
      ElemAbelianRep 3 × DihedralGroup 4) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ ≃*
      order72_E9_D4_sNeg) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ ≃*
      order72_E9_D4_sReflect) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ ≃*
      order72_E9_D4_rNeg) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ ≃*
      order72_E9_D4_rReflect) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ ≃*
      order72_E9_D4_v4NegReflect) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ ≃*
      order72_E9_D4_v4ReflectNeg) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ ≃*
      order72_E9_D4_faithful) := by
  have hFr4 : (φ dr) ^ 4 = 1 := by rw [← map_pow, dr_pow4, map_one]
  have hFs2 : (φ ds) ^ 2 = 1 := by rw [← map_pow, ds_sq, map_one]
  have hcomm : φ ds * φ dr = (φ dr) ^ 3 * φ ds := by
    rw [← map_mul, ds_mul_dr, map_mul, map_pow]
  rcases order72_E9_pow4_cases (φ dr) hFr4 with hF | hF | ⟨θ, hF⟩ | ⟨θ, hF⟩
  · -- `Fr = 1`: the action factors through the `C2` quotient `D4/<r>`.
    rcases order72_E9_sq_cases (φ ds) hFs2 with hG | hG | ⟨θ', hG⟩
    · left
      have hφ : φ = 1 := by apply d4_hom_ext <;> simp [hF, hG]
      exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
    · -- `Fs = -I`: the `sNeg` action.
      right
      left
      have hφ : φ = order72_e9D4SNegAction := by apply d4_hom_ext <;> simp [hF, hG]
      exact ⟨semidirectProductCongr_eq hφ⟩
    · -- `Fs` conjugate to the reflection: transport gives `sReflect`.
      right
      right
      left
      have hφ : (MulAut.conj θ').toMonoidHom.comp φ = order72_e9D4SReflectAction := by
        apply d4_hom_ext
        · change (MulAut.conj θ') (φ dr) = _
          rw [hF, map_one]
          simp
        · change (MulAut.conj θ') (φ ds) = _
          rw [hG]
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ').trans (semidirectProductCongr_eq hφ)⟩
  · -- `Fr = -I`.
    rcases order72_E9_sq_cases (φ ds) hFs2 with hG | hG | ⟨θ', hG⟩
    · -- `Fs = 1`: the `rNeg` action.
      right
      right
      right
      left
      have hφ : φ = order72_e9D4RNegAction := by apply d4_hom_ext <;> simp [hF, hG]
      exact ⟨semidirectProductCongr_eq hφ⟩
    · -- `Fs = -I`: `rNeg` precomposed with the shear `s ↦ s·r`.
      right
      right
      right
      left
      have hφ : φ = order72_e9D4RNegAction.comp order72_D4_shearSR.toMonoidHom := by
        apply d4_hom_ext
        · change φ dr = order72_e9D4RNegAction (order72_D4_shearSR dr)
          rw [hF]
          simp
        · change φ ds = order72_e9D4RNegAction (order72_D4_shearSR ds)
          rw [hG]
          simp [map_mul]
      exact ⟨(semidirectProductCongr_eq hφ).trans
        (semidirectProductCongrAut (φ := order72_e9D4RNegAction) order72_D4_shearSR)⟩
    · -- `Fs` conjugate to the reflection: transport gives `v4NegReflect`.
      right
      right
      right
      right
      right
      left
      have hφ : (MulAut.conj θ').toMonoidHom.comp φ = order72_e9D4V4NegReflectAction := by
        apply d4_hom_ext
        · change (MulAut.conj θ') (φ dr) = order72_e9D4V4NegReflectAction dr
          rw [hF, order72_E9_conj_negAut]
          simp
        · change (MulAut.conj θ') (φ ds) = order72_e9D4V4NegReflectAction ds
          rw [hG]
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ').trans (semidirectProductCongr_eq hφ)⟩
  · -- `Fr` conjugate to the standard reflection; transport and case on `Fs'`.
    have hFs'2 : ((MulAut.conj θ) (φ ds)) ^ 2 = 1 := by
      rw [← map_pow, hFs2, map_one]
    have hr3 : order72_E9_reflectAut ^ 3 = order72_E9_reflectAut := by
      rw [pow_succ, order72_E9_reflectAut_sq, one_mul]
    have hcomm' : Commute ((MulAut.conj θ) (φ ds)) order72_E9_reflectAut := by
      have h3 := congrArg (MulAut.conj θ) hcomm
      rwa [map_mul, map_mul, map_pow, hF, hr3] at h3
    rcases order72_E9_reflect_centralizer_sq_cases ((MulAut.conj θ) (φ ds)) hFs'2 hcomm'
      with hG' | hG' | hG' | hG'
    · -- `Fs' = 1`: the `rReflect` action.
      right
      right
      right
      right
      left
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ = order72_e9D4RReflectAction := by
        apply d4_hom_ext
        · change (MulAut.conj θ) (φ dr) = _
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ ds) = _
          rw [hG']
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans (semidirectProductCongr_eq hφ)⟩
    · -- `Fs' = -I`: the `v4ReflectNeg` action.
      right
      right
      right
      right
      right
      right
      left
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ = order72_e9D4V4ReflectNegAction := by
        apply d4_hom_ext
        · change (MulAut.conj θ) (φ dr) = _
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ ds) = _
          rw [hG']
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans (semidirectProductCongr_eq hφ)⟩
    · -- `Fs' = reflect`: `rReflect` precomposed with the shear `s ↦ s·r`.
      right
      right
      right
      right
      left
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9D4RReflectAction.comp order72_D4_shearSR.toMonoidHom := by
        apply d4_hom_ext
        · change (MulAut.conj θ) (φ dr) =
            order72_e9D4RReflectAction (order72_D4_shearSR dr)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ ds) =
            order72_e9D4RReflectAction (order72_D4_shearSR ds)
          rw [hG']
          simp [map_mul]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9D4RReflectAction)
            order72_D4_shearSR))⟩
    · -- `Fs' = diag(1,-1)`: `v4ReflectNeg` precomposed with the shear `s ↦ s·r`.
      right
      right
      right
      right
      right
      right
      left
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9D4V4ReflectNegAction.comp order72_D4_shearSR.toMonoidHom := by
        apply d4_hom_ext
        · change (MulAut.conj θ) (φ dr) =
            order72_e9D4V4ReflectNegAction (order72_D4_shearSR dr)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ ds) =
            order72_e9D4V4ReflectNegAction (order72_D4_shearSR ds)
          rw [hG']
          simp [map_mul, order72_E9_negAut_mul_reflectAut]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9D4V4ReflectNegAction)
            order72_D4_shearSR))⟩
  · -- `Fr` conjugate to the standard order-`4` element; transport and case on `Fs'`.
    have hFs'2 : ((MulAut.conj θ) (φ ds)) ^ 2 = 1 := by
      rw [← map_pow, hFs2, map_one]
    have hconj' : (MulAut.conj θ) (φ ds) * order72_E9_order4Aut =
        order72_E9_order4Aut ^ 3 * (MulAut.conj θ) (φ ds) := by
      have h3 := congrArg (MulAut.conj θ) hcomm
      rwa [map_mul, map_mul, map_pow, hF] at h3
    rcases order72_E9_order4_d4_partner_cases ((MulAut.conj θ) (φ ds)) hFs'2 hconj'
      with hG' | hG' | hG' | hG'
    · -- `Fs' = reflect`: the faithful action.
      right
      right
      right
      right
      right
      right
      right
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ = order72_e9D4FaithfulAction := by
        apply d4_hom_ext
        · change (MulAut.conj θ) (φ dr) = _
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ ds) = _
          rw [hG']
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans (semidirectProductCongr_eq hφ)⟩
    · -- `Fs' = swap`: the faithful action precomposed with the shear `s ↦ s·r`.
      right
      right
      right
      right
      right
      right
      right
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9D4FaithfulAction.comp order72_D4_shearSR.toMonoidHom := by
        apply d4_hom_ext
        · change (MulAut.conj θ) (φ dr) =
            order72_e9D4FaithfulAction (order72_D4_shearSR dr)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ ds) =
            order72_e9D4FaithfulAction (order72_D4_shearSR ds)
          rw [hG']
          simp [map_mul, order72_E9_reflectAut_mul_order4Aut]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9D4FaithfulAction)
            order72_D4_shearSR))⟩
    · -- `Fs' = diag(1,-1)`: the faithful action precomposed with the squared shear.
      right
      right
      right
      right
      right
      right
      right
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9D4FaithfulAction.comp (order72_D4_shearSR ^ 2).toMonoidHom := by
        apply d4_hom_ext
        · change (MulAut.conj θ) (φ dr) =
            order72_e9D4FaithfulAction ((order72_D4_shearSR ^ 2) dr)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ ds) =
            order72_e9D4FaithfulAction ((order72_D4_shearSR ^ 2) ds)
          rw [hG']
          simp [map_mul, map_pow, order72_E9_order4Aut_sq, order72_E9_reflectAut_mul_negAut]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9D4FaithfulAction)
            (order72_D4_shearSR ^ 2)))⟩
    · -- `Fs' = negated swap`: the faithful action precomposed with the cubed shear.
      right
      right
      right
      right
      right
      right
      right
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9D4FaithfulAction.comp (order72_D4_shearSR ^ 3).toMonoidHom := by
        apply d4_hom_ext
        · change (MulAut.conj θ) (φ dr) =
            order72_e9D4FaithfulAction ((order72_D4_shearSR ^ 3) dr)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ ds) =
            order72_e9D4FaithfulAction ((order72_D4_shearSR ^ 3) ds)
          rw [hG']
          simp [map_mul, map_pow, order72_E9_reflectAut_mul_order4Aut_pow3]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9D4FaithfulAction)
            (order72_D4_shearSR ^ 3)))⟩

/-- The `G`-level version of the `E9 ⋊ D4` classification. -/
theorem order72_e9_d4_branch_cases {G : Type*} [Group G]
    {φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ) :
    Nonempty (G ≃* ElemAbelianRep 3 × DihedralGroup 4) ∨
    Nonempty (G ≃* order72_E9_D4_sNeg) ∨
    Nonempty (G ≃* order72_E9_D4_sReflect) ∨
    Nonempty (G ≃* order72_E9_D4_rNeg) ∨
    Nonempty (G ≃* order72_E9_D4_rReflect) ∨
    Nonempty (G ≃* order72_E9_D4_v4NegReflect) ∨
    Nonempty (G ≃* order72_E9_D4_v4ReflectNeg) ∨
    Nonempty (G ≃* order72_E9_D4_faithful) := by
  rcases order72_e9_d4_semidirect_cases φ with h | h | h | h | h | h | h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inl ⟨e.trans eh⟩)
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩)))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩)))))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))))))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans eh⟩))))))

/-! ### The Sylow-`3`-normal branch, fully classified. -/

/-- The fully classified Sylow-`3`-normal branch: the previous solved cases together
with the direct product and the seven `E9 ⋊ D4` representatives.  These are exactly
the `32` groups of order `72` with normal Sylow `3` and non-normal Sylow `2`, plus the
direct products shared with the Sylow-`2`-normal branch. -/
abbrev order72Sylow3NormalSolvedAllCases (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9AllE9C8H2E8Q8Cases G ∨
    Nonempty (G ≃* ElemAbelianRep 3 × DihedralGroup 4) ∨
      Nonempty (G ≃* order72_E9_D4_sNeg) ∨
        Nonempty (G ≃* order72_E9_D4_sReflect) ∨
          Nonempty (G ≃* order72_E9_D4_rNeg) ∨
            Nonempty (G ≃* order72_E9_D4_rReflect) ∨
              Nonempty (G ≃* order72_E9_D4_v4NegReflect) ∨
                Nonempty (G ≃* order72_E9_D4_v4ReflectNeg) ∨
                  Nonempty (G ≃* order72_E9_D4_faithful)

private theorem order72SolvedAll_of_q8_done {G : Type*} [Group G] :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Q8Done G →
      order72Sylow3NormalSolvedAllCases G := by
  intro hcases
  rcases hcases with hsolved | hrem
  · exact Or.inl hsolved
  · obtain ⟨φ, ⟨e⟩⟩ := hrem
    rcases order72_e9_d4_branch_cases e with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7)))))))

/-- **The Sylow-`3`-normal branch is fully classified**: every group of order `72`
with normal Sylow `3` is isomorphic to one of the explicit representatives. -/
theorem order72_sylow3_normal_rep_cases_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalSolvedAllCases G :=
  order72SolvedAll_of_q8_done
    (order72_partial_rep_cases_c9_all_e9_c8_h2_e8_q8_done_of_sylow_three_normal hG hSyl)

/-- The `n₃ = 1` branch, fully classified. -/
theorem order72_sylow3_normal_rep_cases_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalSolvedAllCases G := by
  exact order72_sylow3_normal_rep_cases_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- Current top-level reduction: the Sylow-`3`-normal branch is completely solved; the
remaining cases are the Sylow-`2`-normal branch (already classified) and the residual
case `n₃ = 4`, `n₂ ≠ 1`. -/
theorem order72_partial_classification_refined_all_e9_done
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalSolvedAllCases G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl (order72_sylow3_normal_rep_cases_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)

end Smallgroups.UsefulTheorems
