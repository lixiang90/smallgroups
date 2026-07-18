/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.E9AutClassify
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Groups of order 72: the `E9 ⋊ H2` cell and the `C9 ⋊ H2` merge

This file classifies the semidirect products `E9 ⋊[φ] H2` with
`H2 = C4 × C2 = Multiplicative (ZMod 4) × Multiplicative (ZMod 2)`.  A homomorphism
`φ : H2 → MulAut (ElemAbelianRep 3) ≅ GL(2,3)` is determined by the commuting images
`F = φ(e₁)` (order dividing `4`) and `G = φ(e₂)` (order dividing `2`).

Up to `Aut(H2) × GL(2,3)`-conjugacy there are exactly **seven** nontrivial orbits
(matching the seven groups `#20, 27, 29, 32, 33, 34, 45` of the GAP census of groups of
order `72` with normal `C3²` and Sylow-`2` of type `C4 × C2`):

* image `C2` (four orbits): `F` or `G` mapping to `-I` or to a reflection —
  `order72_E9_H2_fstNeg`, `order72_E9_H2_sndNeg`, `order72_E9_H2_fstReflect`,
  `order72_E9_H2_sndReflect`;
* image `C4`: `order72_E9_H2_order4`;
* image `V4` (two orbits, since `-I` is fixed by conjugation):
  `order72_E9_H2_v4NegReflect`, `order72_E9_H2_v4ReflectNeg`.

The classification theorem is `order72_e9_h2_semidirect_cases`.  As a small byproduct,
`order72_C9_H2_prodInv_iso_sndInv` shows that the `C9 ⋊ H2` cell has only two nontrivial
isomorphism classes (the third action listed in `H8xP9.lean` differs from the second only
by an automorphism of `H2`), matching the GAP census (`#5, #7`).
-/

namespace Smallgroups.UsefulTheorems

open P3Group

/-- The two standard generators of `H2` commute. -/
theorem h2e1_comm_h2e2 : Commute h2e1 h2e2 := by
  change h2e1 * h2e2 = h2e2 * h2e1
  decide

/-! ### Homomorphisms out of `H2` by generator values. -/

/-- The homomorphism `H2 → A` sending the two standard generators to commuting elements
`F` (of order dividing `4`) and `G` (of order dividing `2`). -/
noncomputable def order72_H2_homOfValues {A : Type*} [Group A] (F G : A)
    (hF4 : F ^ 4 = 1) (hG2 : G ^ 2 = 1) (hcomm : Commute F G) : H2 →* A :=
  (zmodActionHom 4 F hF4).noncommCoprod (zmodActionHom 2 G hG2) fun m n => by
    obtain ⟨i, hi⟩ := ZMod.intCast_surjective (n := 4) (Multiplicative.toAdd m)
    have hm : Multiplicative.ofAdd ((i : ZMod 4)) = m :=
      (congrArg Multiplicative.ofAdd hi).trans (ofAdd_toAdd m)
    obtain ⟨j, hj⟩ := ZMod.intCast_surjective (n := 2) (Multiplicative.toAdd n)
    have hn : Multiplicative.ofAdd ((j : ZMod 2)) = n :=
      (congrArg Multiplicative.ofAdd hj).trans (ofAdd_toAdd n)
    rw [← hm, ← hn]
    simp only [zmodActionHom, zmodZPowHom_intCast]
    exact (hcomm.zpow_left i).zpow_right j

@[simp] theorem order72_H2_homOfValues_e1 {A : Type*} [Group A] (F G : A)
    (hF4 : F ^ 4 = 1) (hG2 : G ^ 2 = 1) (hcomm : Commute F G) :
    order72_H2_homOfValues F G hF4 hG2 hcomm h2e1 = F := by
  simp [order72_H2_homOfValues, h2e1, zmodActionHom_gen]

@[simp] theorem order72_H2_homOfValues_e2 {A : Type*} [Group A] (F G : A)
    (hF4 : F ^ 4 = 1) (hG2 : G ^ 2 = 1) (hcomm : Commute F G) :
    order72_H2_homOfValues F G hF4 hG2 hcomm h2e2 = G := by
  simp [order72_H2_homOfValues, h2e2, zmodActionHom_gen]

/-! ### The seven standard nontrivial actions of `H2` on `C3 × C3`. -/

/-- The action with `e₁ ↦ -I`, `e₂ ↦ 1`. -/
noncomputable abbrev order72_e9H2FstNegAction : H2 →* MulAut (ElemAbelianRep 3) :=
  order72_H2_homOfValues order72_E9_negAut 1
    (by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, order72_E9_negAut_sq, one_pow])
    (one_pow 2) (Commute.one_right _)

/-- The action with `e₁ ↦ 1`, `e₂ ↦ -I`. -/
noncomputable abbrev order72_e9H2SndNegAction : H2 →* MulAut (ElemAbelianRep 3) :=
  order72_H2_homOfValues 1 order72_E9_negAut
    (one_pow 4) order72_E9_negAut_sq (Commute.one_left _)

/-- The action with `e₁ ↦ reflection`, `e₂ ↦ 1`. -/
noncomputable abbrev order72_e9H2FstReflectAction : H2 →* MulAut (ElemAbelianRep 3) :=
  order72_H2_homOfValues order72_E9_reflectAut 1
    (by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, order72_E9_reflectAut_sq, one_pow])
    (one_pow 2) (Commute.one_right _)

/-- The action with `e₁ ↦ 1`, `e₂ ↦ reflection`. -/
noncomputable abbrev order72_e9H2SndReflectAction : H2 →* MulAut (ElemAbelianRep 3) :=
  order72_H2_homOfValues 1 order72_E9_reflectAut
    (one_pow 4) order72_E9_reflectAut_sq (Commute.one_left _)

/-- The action with `e₁ ↦ -I`, `e₂ ↦ reflection` (image `V4`, first orbit). -/
noncomputable abbrev order72_e9H2V4NegReflectAction : H2 →* MulAut (ElemAbelianRep 3) :=
  order72_H2_homOfValues order72_E9_negAut order72_E9_reflectAut
    (by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, order72_E9_negAut_sq, one_pow])
    order72_E9_reflectAut_sq (order72_E9_negAut_central _).symm

/-- The action with `e₁ ↦ reflection`, `e₂ ↦ -I` (image `V4`, second orbit). -/
noncomputable abbrev order72_e9H2V4ReflectNegAction : H2 →* MulAut (ElemAbelianRep 3) :=
  order72_H2_homOfValues order72_E9_reflectAut order72_E9_negAut
    (by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, order72_E9_reflectAut_sq, one_pow])
    order72_E9_negAut_sq (order72_E9_negAut_central _)

/-- The faithful-on-the-first-factor action with `e₁ ↦` order-`4`, `e₂ ↦ 1`. -/
noncomputable abbrev order72_e9H2Order4Action : H2 →* MulAut (ElemAbelianRep 3) :=
  order72_H2_homOfValues order72_E9_order4Aut 1
    order72_E9_order4Aut_pow4 (one_pow 2) (Commute.one_right _)

@[simp] theorem order72_e9H2FstNegAction_e1 :
    order72_e9H2FstNegAction h2e1 = order72_E9_negAut :=
  order72_H2_homOfValues_e1 ..

@[simp] theorem order72_e9H2FstNegAction_e2 : order72_e9H2FstNegAction h2e2 = 1 :=
  order72_H2_homOfValues_e2 ..

@[simp] theorem order72_e9H2SndNegAction_e1 : order72_e9H2SndNegAction h2e1 = 1 :=
  order72_H2_homOfValues_e1 ..

@[simp] theorem order72_e9H2SndNegAction_e2 :
    order72_e9H2SndNegAction h2e2 = order72_E9_negAut :=
  order72_H2_homOfValues_e2 ..

@[simp] theorem order72_e9H2FstReflectAction_e1 :
    order72_e9H2FstReflectAction h2e1 = order72_E9_reflectAut :=
  order72_H2_homOfValues_e1 ..

@[simp] theorem order72_e9H2FstReflectAction_e2 : order72_e9H2FstReflectAction h2e2 = 1 :=
  order72_H2_homOfValues_e2 ..

@[simp] theorem order72_e9H2SndReflectAction_e1 : order72_e9H2SndReflectAction h2e1 = 1 :=
  order72_H2_homOfValues_e1 ..

@[simp] theorem order72_e9H2SndReflectAction_e2 :
    order72_e9H2SndReflectAction h2e2 = order72_E9_reflectAut :=
  order72_H2_homOfValues_e2 ..

@[simp] theorem order72_e9H2V4NegReflectAction_e1 :
    order72_e9H2V4NegReflectAction h2e1 = order72_E9_negAut :=
  order72_H2_homOfValues_e1 ..

@[simp] theorem order72_e9H2V4NegReflectAction_e2 :
    order72_e9H2V4NegReflectAction h2e2 = order72_E9_reflectAut :=
  order72_H2_homOfValues_e2 ..

@[simp] theorem order72_e9H2V4ReflectNegAction_e1 :
    order72_e9H2V4ReflectNegAction h2e1 = order72_E9_reflectAut :=
  order72_H2_homOfValues_e1 ..

@[simp] theorem order72_e9H2V4ReflectNegAction_e2 :
    order72_e9H2V4ReflectNegAction h2e2 = order72_E9_negAut :=
  order72_H2_homOfValues_e2 ..

@[simp] theorem order72_e9H2Order4Action_e1 :
    order72_e9H2Order4Action h2e1 = order72_E9_order4Aut :=
  order72_H2_homOfValues_e1 ..

@[simp] theorem order72_e9H2Order4Action_e2 : order72_e9H2Order4Action h2e2 = 1 :=
  order72_H2_homOfValues_e2 ..

/-- The seven nontrivial representatives of the `E9 ⋊ H2` cell. -/
abbrev order72_E9_H2_fstNeg : Type :=
  SemidirectProduct (ElemAbelianRep 3) H2 order72_e9H2FstNegAction

abbrev order72_E9_H2_sndNeg : Type :=
  SemidirectProduct (ElemAbelianRep 3) H2 order72_e9H2SndNegAction

abbrev order72_E9_H2_fstReflect : Type :=
  SemidirectProduct (ElemAbelianRep 3) H2 order72_e9H2FstReflectAction

abbrev order72_E9_H2_sndReflect : Type :=
  SemidirectProduct (ElemAbelianRep 3) H2 order72_e9H2SndReflectAction

abbrev order72_E9_H2_v4NegReflect : Type :=
  SemidirectProduct (ElemAbelianRep 3) H2 order72_e9H2V4NegReflectAction

abbrev order72_E9_H2_v4ReflectNeg : Type :=
  SemidirectProduct (ElemAbelianRep 3) H2 order72_e9H2V4ReflectNegAction

abbrev order72_E9_H2_order4 : Type :=
  SemidirectProduct (ElemAbelianRep 3) H2 order72_e9H2Order4Action

/-! ### `Aut(H2)` moves used in the classification. -/

/-- The shear `e1 ↦ e1·e2`, `e2 ↦ e2` of `H2`, as a homomorphism. -/
noncomputable abbrev order72_H2_shearFstHom : H2 →* H2 :=
  order72_H2_homOfValues (h2e1 * h2e2) h2e2 (by decide) h2e2sq (by
    change (h2e1 * h2e2) * h2e2 = h2e2 * (h2e1 * h2e2)
    decide)

@[simp] theorem order72_H2_shearFstHom_e1 : order72_H2_shearFstHom h2e1 = h2e1 * h2e2 :=
  order72_H2_homOfValues_e1 ..

@[simp] theorem order72_H2_shearFstHom_e2 : order72_H2_shearFstHom h2e2 = h2e2 :=
  order72_H2_homOfValues_e2 ..

private theorem order72_H2_shearFstHom_sq :
    order72_H2_shearFstHom.comp order72_H2_shearFstHom = MonoidHom.id H2 := by
  apply h2_hom_ext
  · change order72_H2_shearFstHom (order72_H2_shearFstHom h2e1) = h2e1
    rw [order72_H2_shearFstHom_e1, map_mul, order72_H2_shearFstHom_e1,
      order72_H2_shearFstHom_e2]
    decide
  · change order72_H2_shearFstHom (order72_H2_shearFstHom h2e2) = h2e2
    rw [order72_H2_shearFstHom_e2]
    exact order72_H2_shearFstHom_e2

/-- The automorphism of `H2` sending `e1 ↦ e1·e2`, `e2 ↦ e2` (an involution). -/
noncomputable def order72_H2_shearFst : H2 ≃* H2 where
  toFun := order72_H2_shearFstHom
  invFun := order72_H2_shearFstHom
  left_inv x := by
    change (order72_H2_shearFstHom.comp order72_H2_shearFstHom) x = x
    rw [order72_H2_shearFstHom_sq]
    rfl
  right_inv x := by
    change (order72_H2_shearFstHom.comp order72_H2_shearFstHom) x = x
    rw [order72_H2_shearFstHom_sq]
    rfl
  map_mul' := order72_H2_shearFstHom.map_mul

@[simp] theorem order72_H2_shearFst_e1 : order72_H2_shearFst h2e1 = h2e1 * h2e2 :=
  order72_H2_shearFstHom_e1

@[simp] theorem order72_H2_shearFst_e2 : order72_H2_shearFst h2e2 = h2e2 :=
  order72_H2_shearFstHom_e2

/-- The shear `e1 ↦ e1`, `e2 ↦ e1²·e2` of `H2`, as a homomorphism. -/
noncomputable abbrev order72_H2_shearSndSqHom : H2 →* H2 :=
  order72_H2_homOfValues h2e1 (h2z * h2e2) h2e1pow4 (by decide) (by
    change h2e1 * (h2z * h2e2) = (h2z * h2e2) * h2e1
    decide)

@[simp] theorem order72_H2_shearSndSqHom_e1 : order72_H2_shearSndSqHom h2e1 = h2e1 :=
  order72_H2_homOfValues_e1 ..

@[simp] theorem order72_H2_shearSndSqHom_e2 : order72_H2_shearSndSqHom h2e2 = h2z * h2e2 :=
  order72_H2_homOfValues_e2 ..

private theorem order72_H2_shearSndSqHom_z :
    order72_H2_shearSndSqHom h2z = h2z := by
  rw [← h2e1sq, map_pow, order72_H2_shearSndSqHom_e1]

private theorem order72_H2_shearSndSqHom_sq :
    order72_H2_shearSndSqHom.comp order72_H2_shearSndSqHom = MonoidHom.id H2 := by
  apply h2_hom_ext
  · change order72_H2_shearSndSqHom (order72_H2_shearSndSqHom h2e1) = h2e1
    rw [order72_H2_shearSndSqHom_e1]
    exact order72_H2_shearSndSqHom_e1
  · change order72_H2_shearSndSqHom (order72_H2_shearSndSqHom h2e2) = h2e2
    rw [order72_H2_shearSndSqHom_e2, map_mul, order72_H2_shearSndSqHom_z,
      order72_H2_shearSndSqHom_e2]
    decide

/-- The automorphism of `H2` sending `e1 ↦ e1`, `e2 ↦ e1²·e2` (an involution). -/
noncomputable def order72_H2_shearSndSq : H2 ≃* H2 where
  toFun := order72_H2_shearSndSqHom
  invFun := order72_H2_shearSndSqHom
  left_inv x := by
    change (order72_H2_shearSndSqHom.comp order72_H2_shearSndSqHom) x = x
    rw [order72_H2_shearSndSqHom_sq]
    rfl
  right_inv x := by
    change (order72_H2_shearSndSqHom.comp order72_H2_shearSndSqHom) x = x
    rw [order72_H2_shearSndSqHom_sq]
    rfl
  map_mul' := order72_H2_shearSndSqHom.map_mul

@[simp] theorem order72_H2_shearSndSq_e1 : order72_H2_shearSndSq h2e1 = h2e1 :=
  order72_H2_shearSndSqHom_e1

@[simp] theorem order72_H2_shearSndSq_e2 : order72_H2_shearSndSq h2e2 = h2z * h2e2 :=
  order72_H2_shearSndSqHom_e2

/-! ### Auxiliary conjugacy/multiplication facts in `GL(2,3)`. -/

/-- Conjugating the standard reflection by the coordinate swap gives `diag(1, -1)`. -/
theorem order72_E9_conj_swap_reflectAut :
    (MulAut.conj order72_E9_swap) order72_E9_reflectAut = order72_E9_scaleSecond2 := by
  apply order72_E9_autCode_injective
  decide

/-- `-I` times the reflection is `diag(1, -1)`. -/
theorem order72_E9_negAut_mul_reflectAut :
    order72_E9_negAut * order72_E9_reflectAut = order72_E9_scaleSecond2 := by
  apply order72_E9_aut_ext <;> decide

/-- Conjugating `diag(1, -1)` by the coordinate swap gives back the standard reflection
(written in multiplicative form for `simp`). -/
theorem order72_E9_swap_mul_scaleSecond2 :
    order72_E9_swap * order72_E9_scaleSecond2 * order72_E9_swap⁻¹ = order72_E9_reflectAut := by
  apply order72_E9_autCode_injective
  decide

/-- Conjugating the standard reflection by the coordinate swap gives `diag(1, -1)`
(written in multiplicative form for `simp`). -/
theorem order72_E9_swap_mul_reflectAut :
    order72_E9_swap * order72_E9_reflectAut * order72_E9_swap⁻¹ = order72_E9_scaleSecond2 := by
  apply order72_E9_autCode_injective
  decide

/-! ### The classification of the `E9 ⋊ H2` cell. -/

/-- **The `E9 ⋊ H2` cell is fully classified**: every action `H2 → GL(2,3)` gives the
direct product or one of the seven standard nontrivial semidirect products. -/
theorem order72_e9_h2_semidirect_cases (φ : H2 →* MulAut (ElemAbelianRep 3)) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) H2 φ ≃* ElemAbelianRep 3 × H2) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) H2 φ ≃* order72_E9_H2_fstNeg) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) H2 φ ≃* order72_E9_H2_sndNeg) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) H2 φ ≃* order72_E9_H2_fstReflect) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) H2 φ ≃* order72_E9_H2_sndReflect) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) H2 φ ≃* order72_E9_H2_v4NegReflect) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) H2 φ ≃* order72_E9_H2_v4ReflectNeg) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) H2 φ ≃* order72_E9_H2_order4) := by
  have hF4 : (φ h2e1) ^ 4 = 1 := by rw [← map_pow, h2e1pow4, map_one]
  have hG2 : (φ h2e2) ^ 2 = 1 := by rw [← map_pow, h2e2sq, map_one]
  have hcomm : Commute (φ h2e1) (φ h2e2) := h2e1_comm_h2e2.map φ
  rcases order72_E9_pow4_cases (φ h2e1) hF4 with hF | hF | ⟨θ, hF⟩ | ⟨θ, hF⟩
  · -- `F = 1`: the action factors through the `C2` quotient.
    rcases order72_E9_sq_cases (φ h2e2) hG2 with hG | hG | ⟨θ', hG⟩
    · left
      have hφ : φ = 1 := by apply h2_hom_ext <;> simp [hF, hG]
      exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
    · right
      right
      left
      have hφ : φ = order72_e9H2SndNegAction := by apply h2_hom_ext <;> simp [hF, hG]
      exact ⟨semidirectProductCongr_eq hφ⟩
    · right
      right
      right
      right
      left
      have hφ : (MulAut.conj θ').toMonoidHom.comp φ = order72_e9H2SndReflectAction := by
        apply h2_hom_ext
        · change (MulAut.conj θ') (φ h2e1) = _
          rw [hF, map_one]
          simp
        · change (MulAut.conj θ') (φ h2e2) = _
          rw [hG]
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ').trans (semidirectProductCongr_eq hφ)⟩
  · -- `F = -I`.
    rcases order72_E9_sq_cases (φ h2e2) hG2 with hG | hG | ⟨θ', hG⟩
    · right
      left
      have hφ : φ = order72_e9H2FstNegAction := by apply h2_hom_ext <;> simp [hF, hG]
      exact ⟨semidirectProductCongr_eq hφ⟩
    · right
      right
      left
      have hφ : φ = order72_e9H2SndNegAction.comp order72_H2_shearFst.toMonoidHom := by
        apply h2_hom_ext
        · change φ h2e1 = order72_e9H2SndNegAction (order72_H2_shearFst h2e1)
          rw [hF]
          simp
        · change φ h2e2 = order72_e9H2SndNegAction (order72_H2_shearFst h2e2)
          rw [hG]
          simp
      exact ⟨(semidirectProductCongr_eq hφ).trans
        (semidirectProductCongrAut (φ := order72_e9H2SndNegAction) order72_H2_shearFst)⟩
    · right
      right
      right
      right
      right
      left
      have hφ : (MulAut.conj θ').toMonoidHom.comp φ = order72_e9H2V4NegReflectAction := by
        apply h2_hom_ext
        · change (MulAut.conj θ') (φ h2e1) = _
          rw [hF, order72_E9_conj_negAut]
          simp
        · change (MulAut.conj θ') (φ h2e2) = _
          rw [hG]
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ').trans (semidirectProductCongr_eq hφ)⟩
  · -- `F` conjugate to the standard reflection; transport and case on `G'`.
    have hG'2 : ((MulAut.conj θ) (φ h2e2)) ^ 2 = 1 := by
      rw [← map_pow, hG2, map_one]
    have hcomm' : Commute ((MulAut.conj θ) (φ h2e2)) order72_E9_reflectAut := by
      rw [← hF]
      exact (hcomm.map (MulAut.conj θ).toMonoidHom).symm
    rcases order72_E9_reflect_centralizer_sq_cases ((MulAut.conj θ) (φ h2e2)) hG'2 hcomm'
      with hG' | hG' | hG' | hG'
    · right
      right
      right
      left
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ = order72_e9H2FstReflectAction := by
        apply h2_hom_ext
        · change (MulAut.conj θ) (φ h2e1) = _
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ h2e2) = _
          rw [hG']
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans (semidirectProductCongr_eq hφ)⟩
    · right
      right
      right
      right
      right
      right
      left
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ = order72_e9H2V4ReflectNegAction := by
        apply h2_hom_ext
        · change (MulAut.conj θ) (φ h2e1) = _
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ h2e2) = _
          rw [hG']
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans (semidirectProductCongr_eq hφ)⟩
    · right
      right
      right
      right
      left
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9H2SndReflectAction.comp order72_H2_shearFst.toMonoidHom := by
        apply h2_hom_ext
        · change (MulAut.conj θ) (φ h2e1) =
            order72_e9H2SndReflectAction (order72_H2_shearFst h2e1)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ h2e2) =
            order72_e9H2SndReflectAction (order72_H2_shearFst h2e2)
          rw [hG']
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9H2SndReflectAction)
            order72_H2_shearFst))⟩
    · right
      right
      right
      right
      right
      left
      have hχ : (MulAut.conj θ).toMonoidHom.comp φ =
          ((MulAut.conj order72_E9_swap).toMonoidHom.comp order72_e9H2V4NegReflectAction).comp
            order72_H2_shearFst.toMonoidHom := by
        apply h2_hom_ext
        · change (MulAut.conj θ) (φ h2e1) = (MulAut.conj order72_E9_swap)
            (order72_e9H2V4NegReflectAction (order72_H2_shearFst h2e1))
          rw [hF]
          simp [order72_H2_shearFst, map_mul, order72_E9_swap_mul_scaleSecond2,
            order72_E9_negAut_mul_reflectAut]
        · change (MulAut.conj θ) (φ h2e2) = (MulAut.conj order72_E9_swap)
            (order72_e9H2V4NegReflectAction (order72_H2_shearFst h2e2))
          rw [hG']
          simp [order72_H2_shearFst, order72_E9_swap_mul_reflectAut]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hχ).trans
          ((semidirectProductCongrAut
            (φ := (MulAut.conj order72_E9_swap).toMonoidHom.comp
              order72_e9H2V4NegReflectAction) order72_H2_shearFst).trans
            (semidirectProductCongrConj (φ := order72_e9H2V4NegReflectAction)
              order72_E9_swap).symm))⟩
  · -- `F` conjugate to the standard order-`4` element; transport and case on `G'`.
    have hG'2 : ((MulAut.conj θ) (φ h2e2)) ^ 2 = 1 := by
      rw [← map_pow, hG2, map_one]
    have hcomm' : Commute ((MulAut.conj θ) (φ h2e2)) order72_E9_order4Aut := by
      rw [← hF]
      exact (hcomm.map (MulAut.conj θ).toMonoidHom).symm
    rcases order72_E9_order4_centralizer_sq_cases ((MulAut.conj θ) (φ h2e2)) hG'2 hcomm'
      with hG' | hG'
    · right
      right
      right
      right
      right
      right
      right
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ = order72_e9H2Order4Action := by
        apply h2_hom_ext
        · change (MulAut.conj θ) (φ h2e1) = _
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ h2e2) = _
          rw [hG']
          simp
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans (semidirectProductCongr_eq hφ)⟩
    · right
      right
      right
      right
      right
      right
      right
      have hφ : (MulAut.conj θ).toMonoidHom.comp φ =
          order72_e9H2Order4Action.comp order72_H2_shearSndSq.toMonoidHom := by
        apply h2_hom_ext
        · change (MulAut.conj θ) (φ h2e1) =
            order72_e9H2Order4Action (order72_H2_shearSndSq h2e1)
          rw [hF]
          simp
        · change (MulAut.conj θ) (φ h2e2) =
            order72_e9H2Order4Action (order72_H2_shearSndSq h2e2)
          rw [hG']
          simp [← h2e1sq, order72_E9_order4Aut_sq]
      exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
        ((semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9H2Order4Action)
            order72_H2_shearSndSq))⟩

/-- The `G`-level version of the `E9 ⋊ H2` classification. -/
theorem order72_e9_h2_branch_cases {G : Type*} [Group G]
    {φ : H2 →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ) :
    Nonempty (G ≃* ElemAbelianRep 3 × H2) ∨
    Nonempty (G ≃* order72_E9_H2_fstNeg) ∨
    Nonempty (G ≃* order72_E9_H2_sndNeg) ∨
    Nonempty (G ≃* order72_E9_H2_fstReflect) ∨
    Nonempty (G ≃* order72_E9_H2_sndReflect) ∨
    Nonempty (G ≃* order72_E9_H2_v4NegReflect) ∨
    Nonempty (G ≃* order72_E9_H2_v4ReflectNeg) ∨
    Nonempty (G ≃* order72_E9_H2_order4) := by
  rcases order72_e9_h2_semidirect_cases φ with h | h | h | h | h | h | h | h
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

/-! ### The `C9 ⋊ H2` merge: the product-inversion action is the second one up to `Aut(H2)`. -/

/-- The product-inversion `C9 ⋊ H2` is isomorphic to the second-factor inversion one
(precompose the shear `e1 ↦ e1·e2`), so the `C9 ⋊ H2` cell has only **two** nontrivial
isomorphism classes. -/
theorem order72_C9_H2_prodInv_iso_sndInv :
    Nonempty (order72_C9_H2_prodInv ≃* order72_C9_H2_sndInv) := by
  have hφ : order72_c9H2ProdInvAction =
      order72_c9H2SndInvAction.comp order72_H2_shearFst.toMonoidHom := by
    apply h2_hom_ext
    · change order72_c9H2ProdInvAction h2e1 =
        order72_c9H2SndInvAction (order72_H2_shearFst h2e1)
      simp
    · change order72_c9H2ProdInvAction h2e2 =
        order72_c9H2SndInvAction (order72_H2_shearFst h2e2)
      simp
  exact ⟨(semidirectProductCongr_eq hφ).trans
    (semidirectProductCongrAut (φ := order72_c9H2SndInvAction) order72_H2_shearFst)⟩

/-! ### The Sylow-`3`-normal branch with `E9 ⋊ C8` and `E9 ⋊ H2` classified. -/

/-- The fully classified part of the Sylow-`3`-normal branch after solving the
`E9 ⋊ H2` cell: the previous solved cases together with the direct product and the
seven `E9 ⋊ H2` representatives. -/
abbrev order72Sylow3NormalSolvedC9AllE9C8H2Cases (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9AllE9C8Cases G ∨
    Nonempty (G ≃* ElemAbelianRep 3 × H2) ∨
      Nonempty (G ≃* order72_E9_H2_fstNeg) ∨
        Nonempty (G ≃* order72_E9_H2_sndNeg) ∨
          Nonempty (G ≃* order72_E9_H2_fstReflect) ∨
            Nonempty (G ≃* order72_E9_H2_sndReflect) ∨
              Nonempty (G ≃* order72_E9_H2_v4NegReflect) ∨
                Nonempty (G ≃* order72_E9_H2_v4ReflectNeg) ∨
                  Nonempty (G ≃* order72_E9_H2_order4)

/-- The remaining action problems of the Sylow-`3`-normal branch: `E9 ⋊ H` with
`H ∈ {E8, D4, Q8}`. -/
abbrev order72Sylow3NormalRemainingSemidirectCasesE9E8D4Q8 (G : Type*) [Group G] :
    Prop :=
  (∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) ∨
    (∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ))

/-- The Sylow-`3`-normal branch with the `C9 ⋊ H`, `E9 ⋊ C8` and `E9 ⋊ H2` cells fully
classified: the remaining cases are exactly the three `E9 ⋊ H` action problems with
`H ∈ {E8, D4, Q8}`. -/
abbrev order72Sylow3NormalPartialRepCasesC9AllE9C8H2Done (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9AllE9C8H2Cases G ∨
    order72Sylow3NormalRemainingSemidirectCasesE9E8D4Q8 G

private theorem order72PartialC9AllE9C8H2Done_of_e9_c8_done {G : Type*} [Group G] :
    order72Sylow3NormalPartialRepCasesC9AllE9C8Done G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8H2Done G := by
  intro hcases
  rcases hcases with hsolved | hrem
  · left
    left
    exact hsolved
  · rcases hrem with hH2 | hE8 | hD4 | hQ8
    · obtain ⟨φ, ⟨e⟩⟩ := hH2
      rcases order72_e9_h2_branch_cases e with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
      · left
        right
        left
        exact h0
      · left
        right
        right
        left
        exact h1
      · left
        right
        right
        right
        left
        exact h2
      · left
        right
        right
        right
        right
        left
        exact h3
      · left
        right
        right
        right
        right
        right
        left
        exact h4
      · left
        right
        right
        right
        right
        right
        right
        left
        exact h5
      · left
        right
        right
        right
        right
        right
        right
        right
        left
        exact h6
      · left
        right
        right
        right
        right
        right
        right
        right
        right
        exact h7
    · right
      left
      exact hE8
    · right
      right
      left
      exact hD4
    · right
      right
      right
      exact hQ8

theorem order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_h2_done
    {G : Type*} [Group G] :
    order72Sylow3NormalSemidirectCases G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8H2Done G := by
  intro hcases
  exact order72PartialC9AllE9C8H2Done_of_e9_c8_done
    (order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_done hcases)

/-- The `n₃ = 1` branch with all `C9 ⋊ H`, `E9 ⋊ C8` and `E9 ⋊ H2` cases reduced to
explicit representatives. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_h2_done_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2Done G :=
  order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_h2_done
    (order72_semidirectProduct_standard_cases_of_sylow_three_normal hG hSyl)

/-- The `n₃ = 1` branch with all `C9 ⋊ H`, `E9 ⋊ C8` and `E9 ⋊ H2` cases reduced to
explicit representatives. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_h2_done_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2Done G := by
  exact order72_partial_rep_cases_c9_all_e9_c8_h2_done_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- Current top-level reduction: in the Sylow-`3`-normal branch every `C9 ⋊ H`,
`E9 ⋊ C8` and `E9 ⋊ H2` case is now explicit; the remaining semidirect action problems
are `E9 ⋊ E8`, `E9 ⋊ D4` and `E9 ⋊ Q8`. -/
theorem order72_partial_classification_refined_c9_all_e9_c8_h2_done
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2Done G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl
      (order72_partial_rep_cases_c9_all_e9_c8_h2_done_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)

end Smallgroups.UsefulTheorems
