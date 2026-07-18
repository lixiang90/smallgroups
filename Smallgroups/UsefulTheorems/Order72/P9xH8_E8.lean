/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.P9xH8_H2

/-!
# Groups of order 72: the `E9 ⋊ E8` cell

This file classifies the semidirect products `E9 ⋊[φ] E8` with
`E8 = (C2)³`.  A homomorphism `φ : E8 → MulAut (ElemAbelianRep 3) ≅ GL(2,3)` is
determined by three pairwise commuting involutions `Fᵢ = φ(eᵢ)`.  The elementary abelian
`2`-subgroups of `GL(2,3)` are `{1}`, `C2` (either `{1, -I}` or a reflection subgroup,
each one conjugacy class) and `V4 = {1, -I, R, -R}` (one conjugacy class), so up to
`Aut(E8) × GL(2,3)`-conjugacy there are exactly **three** nontrivial orbits (matching
the GAP census groups `#46, 48, 49` of order `72` with normal `C3²` and elementary
abelian Sylow-`2`):

* `order72_E9_E8_neg100`: image `{1, -I}`;
* `order72_E9_E8_reflect100`: image a reflection subgroup;
* `order72_E9_E8_v4`: image `V4`.

The classification theorem is `order72_e9_e8_semidirect_cases`.
-/

namespace Smallgroups.UsefulTheorems

open P3Group

/-! ### Generators of `E8` and homomorphism extensionality. -/

/-- The first standard generator of `E8 = (ZMod 2)³`. -/
def e8e1 : E8 := (Multiplicative.ofAdd (1 : ZMod 2), (1, 1))

/-- The second standard generator of `E8`. -/
def e8e2 : E8 := (1, (Multiplicative.ofAdd (1 : ZMod 2), 1))

/-- The third standard generator of `E8`. -/
def e8e3 : E8 := (1, (1, Multiplicative.ofAdd (1 : ZMod 2)))

theorem e8e1sq : e8e1 ^ 2 = 1 := by decide
theorem e8e2sq : e8e2 ^ 2 = 1 := by decide
theorem e8e3sq : e8e3 ^ 2 = 1 := by decide

theorem e8e1_comm_e8e2 : Commute e8e1 e8e2 := by
  change e8e1 * e8e2 = e8e2 * e8e1
  decide

theorem e8e1_comm_e8e3 : Commute e8e1 e8e3 := by
  change e8e1 * e8e3 = e8e3 * e8e1
  decide

theorem e8e2_comm_e8e3 : Commute e8e2 e8e3 := by
  change e8e2 * e8e3 = e8e3 * e8e2
  decide

/-- The eight elements of `E8` as monomials in the standard generators. -/
theorem e8gen : ∀ x : E8, x = 1 ∨ x = e8e1 ∨ x = e8e2 ∨ x = e8e1 * e8e2 ∨
    x = e8e3 ∨ x = e8e1 * e8e3 ∨ x = e8e2 * e8e3 ∨ x = e8e1 * e8e2 * e8e3 := by
  decide

/-- Homomorphisms out of `(ZMod 2)³` are determined by the three standard generators. -/
theorem e8_hom_ext {M : Type*} [Group M] {φ ψ : E8 →* M}
    (h1 : φ e8e1 = ψ e8e1) (h2 : φ e8e2 = ψ e8e2) (h3 : φ e8e3 = ψ e8e3) : φ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases e8gen x with h | h | h | h | h | h | h | h <;> subst h <;>
    simp [map_mul, map_one, h1, h2, h3]

/-- The homomorphism `E8 → A` sending the three standard generators to pairwise
commuting involutions `F1, F2, F3`. -/
noncomputable def order72_E8_homOfValues {A : Type*} [Group A] (F1 F2 F3 : A)
    (h1 : F1 ^ 2 = 1) (h2 : F2 ^ 2 = 1) (h3 : F3 ^ 2 = 1)
    (c12 : Commute F1 F2) (c13 : Commute F1 F3) (c23 : Commute F2 F3) : E8 →* A :=
  (zmodActionHom 2 F1 h1).noncommCoprod
    ((zmodActionHom 2 F2 h2).noncommCoprod (zmodActionHom 2 F3 h3) fun m n => by
      obtain ⟨i, hi⟩ := ZMod.intCast_surjective (n := 2) (Multiplicative.toAdd m)
      have hm : Multiplicative.ofAdd ((i : ZMod 2)) = m :=
        (congrArg Multiplicative.ofAdd hi).trans (ofAdd_toAdd m)
      obtain ⟨j, hj⟩ := ZMod.intCast_surjective (n := 2) (Multiplicative.toAdd n)
      have hn : Multiplicative.ofAdd ((j : ZMod 2)) = n :=
        (congrArg Multiplicative.ofAdd hj).trans (ofAdd_toAdd n)
      rw [← hm, ← hn]
      simp only [zmodActionHom, zmodZPowHom_intCast]
      exact (c23.zpow_left i).zpow_right j)
    fun m n => by
      obtain ⟨i, hi⟩ := ZMod.intCast_surjective (n := 2) (Multiplicative.toAdd m)
      have hm : Multiplicative.ofAdd ((i : ZMod 2)) = m :=
        (congrArg Multiplicative.ofAdd hi).trans (ofAdd_toAdd m)
      obtain ⟨j, hj⟩ := ZMod.intCast_surjective (n := 2) (Multiplicative.toAdd n.1)
      have hn1 : Multiplicative.ofAdd ((j : ZMod 2)) = n.1 :=
        (congrArg Multiplicative.ofAdd hj).trans (ofAdd_toAdd n.1)
      obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := 2) (Multiplicative.toAdd n.2)
      have hn2 : Multiplicative.ofAdd ((k : ZMod 2)) = n.2 :=
        (congrArg Multiplicative.ofAdd hk).trans (ofAdd_toAdd n.2)
      rw [← hm, MonoidHom.noncommCoprod_apply, ← hn1, ← hn2]
      simp only [zmodActionHom, zmodZPowHom_intCast]
      exact ((c12.zpow_left i).zpow_right j).mul_right ((c13.zpow_left i).zpow_right k)

@[simp] theorem order72_E8_homOfValues_e1 {A : Type*} [Group A] (F1 F2 F3 : A)
    (h1 : F1 ^ 2 = 1) (h2 : F2 ^ 2 = 1) (h3 : F3 ^ 2 = 1)
    (c12 : Commute F1 F2) (c13 : Commute F1 F3) (c23 : Commute F2 F3) :
    order72_E8_homOfValues F1 F2 F3 h1 h2 h3 c12 c13 c23 e8e1 = F1 := by
  simp [order72_E8_homOfValues, e8e1, zmodActionHom_gen]

@[simp] theorem order72_E8_homOfValues_e2 {A : Type*} [Group A] (F1 F2 F3 : A)
    (h1 : F1 ^ 2 = 1) (h2 : F2 ^ 2 = 1) (h3 : F3 ^ 2 = 1)
    (c12 : Commute F1 F2) (c13 : Commute F1 F3) (c23 : Commute F2 F3) :
    order72_E8_homOfValues F1 F2 F3 h1 h2 h3 c12 c13 c23 e8e2 = F2 := by
  simp [order72_E8_homOfValues, e8e2, zmodActionHom_gen]

@[simp] theorem order72_E8_homOfValues_e3 {A : Type*} [Group A] (F1 F2 F3 : A)
    (h1 : F1 ^ 2 = 1) (h2 : F2 ^ 2 = 1) (h3 : F3 ^ 2 = 1)
    (c12 : Commute F1 F2) (c13 : Commute F1 F3) (c23 : Commute F2 F3) :
    order72_E8_homOfValues F1 F2 F3 h1 h2 h3 c12 c13 c23 e8e3 = F3 := by
  simp [order72_E8_homOfValues, e8e3, zmodActionHom_gen]

/-! ### `Aut(E8)` moves (all involutions, by generators' images). -/

/-- Builds an involutive automorphism of `E8` from an involutive homomorphism. -/
private noncomputable def order72_E8_equivOfHomSq (θ : E8 →* E8)
    (hθ : θ.comp θ = MonoidHom.id E8) : E8 ≃* E8 where
  toFun := θ
  invFun := θ
  left_inv x := by
    change (θ.comp θ) x = x
    rw [hθ]
    rfl
  right_inv x := by
    change (θ.comp θ) x = x
    rw [hθ]
    rfl
  map_mul' := θ.map_mul

/-- The automorphism of `E8` swapping `e1 ↔ e2`. -/
noncomputable def order72_E8_swap12 : E8 ≃* E8 :=
  order72_E8_equivOfHomSq
    (order72_E8_homOfValues e8e2 e8e1 e8e3 e8e2sq e8e1sq e8e3sq
      e8e1_comm_e8e2.symm e8e2_comm_e8e3 e8e1_comm_e8e3.symm) (by
    apply e8_hom_ext <;> simp)

/-- The automorphism of `E8` swapping `e1 ↔ e3`. -/
noncomputable def order72_E8_swap13 : E8 ≃* E8 :=
  order72_E8_equivOfHomSq
    (order72_E8_homOfValues e8e3 e8e2 e8e1 e8e3sq e8e2sq e8e1sq
      e8e2_comm_e8e3 e8e1_comm_e8e3.symm e8e1_comm_e8e2.symm) (by
    apply e8_hom_ext <;> simp)

/-- The automorphism of `E8` swapping `e2 ↔ e3`. -/
noncomputable def order72_E8_swap23 : E8 ≃* E8 :=
  order72_E8_equivOfHomSq
    (order72_E8_homOfValues e8e1 e8e3 e8e2 e8e1sq e8e3sq e8e2sq
      e8e1_comm_e8e3.symm e8e1_comm_e8e2.symm e8e2_comm_e8e3.symm) (by
    apply e8_hom_ext <;> simp)

/-- The automorphism of `E8` shearing `e2 ↦ e1·e2`. -/
noncomputable def order72_E8_shear12 : E8 ≃* E8 :=
  order72_E8_equivOfHomSq
    (order72_E8_homOfValues e8e1 (e8e1 * e8e2) e8e3 e8e1sq (by decide) e8e3sq
      (by
        change e8e1 * (e8e1 * e8e2) = (e8e1 * e8e2) * e8e1
        decide)
      e8e1_comm_e8e3 (by
        change (e8e1 * e8e2) * e8e3 = e8e3 * (e8e1 * e8e2)
        decide)) (by
    apply e8_hom_ext <;> simp [← mul_assoc, ← pow_two, e8e1sq])

/-- The automorphism of `E8` shearing `e3 ↦ e1·e3`. -/
noncomputable def order72_E8_shear13 : E8 ≃* E8 :=
  order72_E8_equivOfHomSq
    (order72_E8_homOfValues e8e1 e8e2 (e8e1 * e8e3) e8e1sq e8e2sq (by decide)
      e8e1_comm_e8e2 (by
        change e8e1 * (e8e1 * e8e3) = (e8e1 * e8e3) * e8e1
        decide)
      (by
        change e8e2 * (e8e1 * e8e3) = (e8e1 * e8e3) * e8e2
        decide)) (by
    apply e8_hom_ext <;> simp [← mul_assoc, ← pow_two, e8e1sq])

/-- The automorphism of `E8` shearing `e3 ↦ e2·e3`. -/
noncomputable def order72_E8_shear23 : E8 ≃* E8 :=
  order72_E8_equivOfHomSq
    (order72_E8_homOfValues e8e1 e8e2 (e8e2 * e8e3) e8e1sq e8e2sq (by decide)
      e8e1_comm_e8e2 (by
        change e8e1 * (e8e2 * e8e3) = (e8e2 * e8e3) * e8e1
        decide)
      (by
        change e8e2 * (e8e2 * e8e3) = (e8e2 * e8e3) * e8e2
        decide)) (by
    apply e8_hom_ext <;> simp [← mul_assoc, ← pow_two, e8e2sq])

/-! ### The three standard actions of `E8` on `C3 × C3`. -/

/-- The action with `e1 ↦ -I`, `e2, e3 ↦ 1`. -/
noncomputable abbrev order72_e9E8Neg100Action : E8 →* MulAut (ElemAbelianRep 3) :=
  order72_E8_homOfValues order72_E9_negAut 1 1
    order72_E9_negAut_sq (one_pow 2) (one_pow 2)
    (Commute.one_right _) (Commute.one_right _) (Commute.one_right _)

/-- The action with `e1 ↦ reflection`, `e2, e3 ↦ 1`. -/
noncomputable abbrev order72_e9E8Reflect100Action : E8 →* MulAut (ElemAbelianRep 3) :=
  order72_E8_homOfValues order72_E9_reflectAut 1 1
    order72_E9_reflectAut_sq (one_pow 2) (one_pow 2)
    (Commute.one_right _) (Commute.one_right _) (Commute.one_right _)

/-- The action with `e1 ↦ -I`, `e2 ↦ reflection`, `e3 ↦ 1` (image `V4`). -/
noncomputable abbrev order72_e9E8V4Action : E8 →* MulAut (ElemAbelianRep 3) :=
  order72_E8_homOfValues order72_E9_negAut order72_E9_reflectAut 1
    order72_E9_negAut_sq order72_E9_reflectAut_sq (one_pow 2)
    (order72_E9_negAut_central _).symm (Commute.one_right _) (Commute.one_right _)

/-- The three nontrivial representatives of the `E9 ⋊ E8` cell. -/
abbrev order72_E9_E8_neg100 : Type :=
  SemidirectProduct (ElemAbelianRep 3) E8 order72_e9E8Neg100Action

abbrev order72_E9_E8_reflect100 : Type :=
  SemidirectProduct (ElemAbelianRep 3) E8 order72_e9E8Reflect100Action

abbrev order72_E9_E8_v4 : Type :=
  SemidirectProduct (ElemAbelianRep 3) E8 order72_e9E8V4Action

/-! ### Bridge simp lemmas for the `Aut(E8)` moves and the standard actions. -/

@[simp] theorem order72_E8_swap12_e1 : order72_E8_swap12 e8e1 = e8e2 := by
  simp [order72_E8_swap12, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_swap12_e2 : order72_E8_swap12 e8e2 = e8e1 := by
  simp [order72_E8_swap12, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_swap12_e3 : order72_E8_swap12 e8e3 = e8e3 := by
  simp [order72_E8_swap12, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_swap13_e1 : order72_E8_swap13 e8e1 = e8e3 := by
  simp [order72_E8_swap13, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_swap13_e2 : order72_E8_swap13 e8e2 = e8e2 := by
  simp [order72_E8_swap13, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_swap13_e3 : order72_E8_swap13 e8e3 = e8e1 := by
  simp [order72_E8_swap13, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_swap23_e1 : order72_E8_swap23 e8e1 = e8e1 := by
  simp [order72_E8_swap23, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_swap23_e2 : order72_E8_swap23 e8e2 = e8e3 := by
  simp [order72_E8_swap23, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_swap23_e3 : order72_E8_swap23 e8e3 = e8e2 := by
  simp [order72_E8_swap23, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_shear12_e1 : order72_E8_shear12 e8e1 = e8e1 := by
  simp [order72_E8_shear12, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_shear12_e2 : order72_E8_shear12 e8e2 = e8e1 * e8e2 := by
  simp [order72_E8_shear12, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_shear12_e3 : order72_E8_shear12 e8e3 = e8e3 := by
  simp [order72_E8_shear12, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_shear13_e1 : order72_E8_shear13 e8e1 = e8e1 := by
  simp [order72_E8_shear13, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_shear13_e2 : order72_E8_shear13 e8e2 = e8e2 := by
  simp [order72_E8_shear13, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_shear13_e3 : order72_E8_shear13 e8e3 = e8e1 * e8e3 := by
  simp [order72_E8_shear13, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_shear23_e1 : order72_E8_shear23 e8e1 = e8e1 := by
  simp [order72_E8_shear23, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_shear23_e2 : order72_E8_shear23 e8e2 = e8e2 := by
  simp [order72_E8_shear23, order72_E8_equivOfHomSq]

@[simp] theorem order72_E8_shear23_e3 : order72_E8_shear23 e8e3 = e8e2 * e8e3 := by
  simp [order72_E8_shear23, order72_E8_equivOfHomSq]

@[simp] theorem order72_e9E8Neg100Action_e1 :
    order72_e9E8Neg100Action e8e1 = order72_E9_negAut :=
  order72_E8_homOfValues_e1 ..

@[simp] theorem order72_e9E8Neg100Action_e2 : order72_e9E8Neg100Action e8e2 = 1 :=
  order72_E8_homOfValues_e2 ..

@[simp] theorem order72_e9E8Neg100Action_e3 : order72_e9E8Neg100Action e8e3 = 1 :=
  order72_E8_homOfValues_e3 ..

@[simp] theorem order72_e9E8Reflect100Action_e1 :
    order72_e9E8Reflect100Action e8e1 = order72_E9_reflectAut :=
  order72_E8_homOfValues_e1 ..

@[simp] theorem order72_e9E8Reflect100Action_e2 : order72_e9E8Reflect100Action e8e2 = 1 :=
  order72_E8_homOfValues_e2 ..

@[simp] theorem order72_e9E8Reflect100Action_e3 : order72_e9E8Reflect100Action e8e3 = 1 :=
  order72_E8_homOfValues_e3 ..

@[simp] theorem order72_e9E8V4Action_e1 :
    order72_e9E8V4Action e8e1 = order72_E9_negAut :=
  order72_E8_homOfValues_e1 ..

@[simp] theorem order72_e9E8V4Action_e2 :
    order72_e9E8V4Action e8e2 = order72_E9_reflectAut :=
  order72_E8_homOfValues_e2 ..

@[simp] theorem order72_e9E8V4Action_e3 : order72_e9E8V4Action e8e3 = 1 :=
  order72_E8_homOfValues_e3 ..

/-! ### Product facts in `GL(2,3)` used by the case analysis. -/

theorem order72_E9_negAut_mul_self : order72_E9_negAut * order72_E9_negAut = 1 := by
  rw [← pow_two]
  exact order72_E9_negAut_sq

theorem order72_E9_reflectAut_mul_self : order72_E9_reflectAut * order72_E9_reflectAut = 1 := by
  rw [← pow_two]
  exact order72_E9_reflectAut_sq

theorem order72_E9_reflectAut_mul_scaleSecond2 :
    order72_E9_reflectAut * order72_E9_scaleSecond2 = order72_E9_negAut := by
  apply order72_E9_aut_ext <;> decide

theorem order72_E9_scaleSecond2_mul_reflectAut :
    order72_E9_scaleSecond2 * order72_E9_reflectAut = order72_E9_negAut := by
  apply order72_E9_aut_ext <;> decide

theorem order72_E9_reflectAut_mul_negAut :
    order72_E9_reflectAut * order72_E9_negAut = order72_E9_scaleSecond2 := by
  apply order72_E9_aut_ext <;> decide

/-- Conjugating `diag(1,-1)` by the coordinate swap gives the standard reflection. -/
theorem order72_E9_conj_swap_scaleSecond2 :
    (MulAut.conj order72_E9_swap) order72_E9_scaleSecond2 = order72_E9_reflectAut := by
  apply order72_E9_autCode_injective
  decide

/-- Two-step precomposition of the action with automorphisms of the source. -/
private noncomputable def order72_e9_e8_congrAut2 (χ : E8 →* MulAut (ElemAbelianRep 3))
    (δ1 δ2 : E8 ≃* E8) :
    SemidirectProduct (ElemAbelianRep 3) E8 (χ.comp (δ1.toMonoidHom.comp δ2.toMonoidHom)) ≃*
      SemidirectProduct (ElemAbelianRep 3) E8 χ :=
  (semidirectProductCongr_eq (MonoidHom.comp_assoc δ2.toMonoidHom δ1.toMonoidHom χ).symm).trans
    ((semidirectProductCongrAut (φ := χ.comp δ1.toMonoidHom) δ2).trans
      (semidirectProductCongrAut (φ := χ) δ1))

/-- Three-step precomposition of the action with automorphisms of the source. -/
private noncomputable def order72_e9_e8_congrAut3 (χ : E8 →* MulAut (ElemAbelianRep 3))
    (δ1 δ2 δ3 : E8 ≃* E8) :
    SemidirectProduct (ElemAbelianRep 3) E8
        (χ.comp (δ1.toMonoidHom.comp (δ2.toMonoidHom.comp δ3.toMonoidHom))) ≃*
      SemidirectProduct (ElemAbelianRep 3) E8 χ :=
  (semidirectProductCongr_eq
    (MonoidHom.comp_assoc (δ2.toMonoidHom.comp δ3.toMonoidHom) δ1.toMonoidHom χ).symm).trans
    ((order72_e9_e8_congrAut2 (χ.comp δ1.toMonoidHom) δ2 δ3).trans
      (semidirectProductCongrAut (φ := χ) δ1))

/-- Four-step precomposition of the action with automorphisms of the source. -/
private noncomputable def order72_e9_e8_congrAut4 (χ : E8 →* MulAut (ElemAbelianRep 3))
    (δ1 δ2 δ3 δ4 : E8 ≃* E8) :
    SemidirectProduct (ElemAbelianRep 3) E8
        (χ.comp (δ1.toMonoidHom.comp (δ2.toMonoidHom.comp
          (δ3.toMonoidHom.comp δ4.toMonoidHom)))) ≃*
      SemidirectProduct (ElemAbelianRep 3) E8 χ :=
  (semidirectProductCongr_eq
    (MonoidHom.comp_assoc (δ2.toMonoidHom.comp (δ3.toMonoidHom.comp δ4.toMonoidHom))
      δ1.toMonoidHom χ).symm).trans
    ((order72_e9_e8_congrAut3 (χ.comp δ1.toMonoidHom) δ2 δ3 δ4).trans
      (semidirectProductCongrAut (φ := χ) δ1))

/-! ### The classification of the `E9 ⋊ E8` cell. -/

/-- **The `E9 ⋊ E8` cell is fully classified**: every action `E8 → GL(2,3)` gives the
direct product or one of the three standard nontrivial semidirect products. -/
theorem order72_e9_e8_semidirect_cases (φ : E8 →* MulAut (ElemAbelianRep 3)) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) E8 φ ≃* ElemAbelianRep 3 × E8) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) E8 φ ≃* order72_E9_E8_neg100) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) E8 φ ≃* order72_E9_E8_reflect100) ∨
    Nonempty (SemidirectProduct (ElemAbelianRep 3) E8 φ ≃* order72_E9_E8_v4) := by
  have hF1 : (φ e8e1) ^ 2 = 1 := by rw [← map_pow, e8e1sq, map_one]
  have hF2 : (φ e8e2) ^ 2 = 1 := by rw [← map_pow, e8e2sq, map_one]
  have hF3 : (φ e8e3) ^ 2 = 1 := by rw [← map_pow, e8e3sq, map_one]
  have c12 : Commute (φ e8e1) (φ e8e2) := e8e1_comm_e8e2.map φ
  have c13 : Commute (φ e8e1) (φ e8e3) := e8e1_comm_e8e3.map φ
  have c23 : Commute (φ e8e2) (φ e8e3) := e8e2_comm_e8e3.map φ
  rcases order72_E9_sq_cases (φ e8e1) hF1 with h1 | h1 | ⟨θ1, h1⟩
  · -- `F1 = 1`.
    rcases order72_E9_sq_cases (φ e8e2) hF2 with h2 | h2 | ⟨θ2, h2⟩
    · -- `F2 = 1`.
      rcases order72_E9_sq_cases (φ e8e3) hF3 with h3 | h3 | ⟨θ3, h3⟩
      · left
        have hφ : φ = 1 := by apply e8_hom_ext <;> simp [h1, h2, h3]
        exact ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
      · right
        left
        have hφ : φ = order72_e9E8Neg100Action.comp order72_E8_swap13.toMonoidHom := by
          apply e8_hom_ext <;> simp [h1, h2, h3]
        exact ⟨(semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9E8Neg100Action) order72_E8_swap13)⟩
      · right
        right
        left
        have hφ : (MulAut.conj θ3).toMonoidHom.comp φ =
            order72_e9E8Reflect100Action.comp order72_E8_swap13.toMonoidHom := by
          apply e8_hom_ext
          · change (MulAut.conj θ3) (φ e8e1) = _
            rw [h1, map_one]
            simp
          · change (MulAut.conj θ3) (φ e8e2) = _
            rw [h2, map_one]
            simp
          · change (MulAut.conj θ3) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ3).trans
          ((semidirectProductCongr_eq hφ).trans
            (semidirectProductCongrAut (φ := order72_e9E8Reflect100Action)
              order72_E8_swap13))⟩
    · -- `F2 = -I`.
      rcases order72_E9_sq_cases (φ e8e3) hF3 with h3 | h3 | ⟨θ3, h3⟩
      · right
        left
        have hφ : φ = order72_e9E8Neg100Action.comp order72_E8_swap12.toMonoidHom := by
          apply e8_hom_ext <;> simp [h1, h2, h3]
        exact ⟨(semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9E8Neg100Action) order72_E8_swap12)⟩
      · right
        left
        have hφ : φ = order72_e9E8Neg100Action.comp
            (order72_E8_swap12.toMonoidHom.comp order72_E8_shear23.toMonoidHom) := by
          apply e8_hom_ext <;> simp [h1, h2, h3]
        exact ⟨(semidirectProductCongr_eq hφ).trans
          (order72_e9_e8_congrAut2 order72_e9E8Neg100Action order72_E8_swap12
            order72_E8_shear23)⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ3).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_swap12.toMonoidHom.comp order72_E8_swap13.toMonoidHom) := by
          apply e8_hom_ext
          · change (MulAut.conj θ3) (φ e8e1) = _
            rw [h1, map_one]
            simp
          · change (MulAut.conj θ3) (φ e8e2) = _
            rw [h2, order72_E9_conj_negAut]
            simp
          · change (MulAut.conj θ3) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ3).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut2 order72_e9E8V4Action order72_E8_swap12
              order72_E8_swap13))⟩
    · -- `F2` conjugate to the standard reflection.
      have hF3'2 : ((MulAut.conj θ2) (φ e8e3)) ^ 2 = 1 := by
        rw [← map_pow, hF3, map_one]
      have hcomm3' : Commute ((MulAut.conj θ2) (φ e8e3)) order72_E9_reflectAut := by
        rw [← h2]
        exact (c23.map (MulAut.conj θ2).toMonoidHom).symm
      rcases order72_E9_reflect_centralizer_sq_cases ((MulAut.conj θ2) (φ e8e3)) hF3'2
        hcomm3' with h3 | h3 | h3 | h3
      · right
        right
        left
        have hφ : (MulAut.conj θ2).toMonoidHom.comp φ =
            order72_e9E8Reflect100Action.comp order72_E8_swap12.toMonoidHom := by
          apply e8_hom_ext
          · change (MulAut.conj θ2) (φ e8e1) = _
            rw [h1, map_one]
            simp
          · change (MulAut.conj θ2) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ2) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ2).trans
          ((semidirectProductCongr_eq hφ).trans
            (semidirectProductCongrAut (φ := order72_e9E8Reflect100Action)
              order72_E8_swap12))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ2).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp order72_E8_swap13.toMonoidHom := by
          apply e8_hom_ext
          · change (MulAut.conj θ2) (φ e8e1) = _
            rw [h1, map_one]
            simp
          · change (MulAut.conj θ2) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ2) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ2).trans
          ((semidirectProductCongr_eq hφ).trans
            (semidirectProductCongrAut (φ := order72_e9E8V4Action) order72_E8_swap13))⟩
      · right
        right
        left
        have hφ : (MulAut.conj θ2).toMonoidHom.comp φ =
            order72_e9E8Reflect100Action.comp
              (order72_E8_swap12.toMonoidHom.comp order72_E8_shear23.toMonoidHom) := by
          apply e8_hom_ext
          · change (MulAut.conj θ2) (φ e8e1) = _
            rw [h1, map_one]
            simp
          · change (MulAut.conj θ2) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ2) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ2).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut2 order72_e9E8Reflect100Action order72_E8_swap12
              order72_E8_shear23))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ2).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_swap13.toMonoidHom.comp order72_E8_shear23.toMonoidHom) := by
          apply e8_hom_ext
          · change (MulAut.conj θ2) (φ e8e1) = _
            rw [h1, map_one]
            simp
          · change (MulAut.conj θ2) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ2) (φ e8e3) = _
            rw [h3]
            simp [order72_E9_reflectAut_mul_negAut]
        exact ⟨(semidirectProductCongrConj (φ := φ) θ2).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut2 order72_e9E8V4Action order72_E8_swap13
              order72_E8_shear23))⟩
  · -- `F1 = -I`.
    rcases order72_E9_sq_cases (φ e8e2) hF2 with h2 | h2 | ⟨θ2, h2⟩
    · -- `F2 = 1`.
      rcases order72_E9_sq_cases (φ e8e3) hF3 with h3 | h3 | ⟨θ3, h3⟩
      · right
        left
        have hφ : φ = order72_e9E8Neg100Action := by
          apply e8_hom_ext <;> simp [h1, h2, h3]
        exact ⟨semidirectProductCongr_eq hφ⟩
      · right
        left
        have hφ : φ = order72_e9E8Neg100Action.comp order72_E8_shear13.toMonoidHom := by
          apply e8_hom_ext <;> simp [h1, h2, h3]
        exact ⟨(semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9E8Neg100Action) order72_E8_shear13)⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ3).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp order72_E8_swap23.toMonoidHom := by
          apply e8_hom_ext
          · change (MulAut.conj θ3) (φ e8e1) = _
            rw [h1, order72_E9_conj_negAut]
            simp
          · change (MulAut.conj θ3) (φ e8e2) = _
            rw [h2, map_one]
            simp
          · change (MulAut.conj θ3) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ3).trans
          ((semidirectProductCongr_eq hφ).trans
            (semidirectProductCongrAut (φ := order72_e9E8V4Action) order72_E8_swap23))⟩
    · -- `F2 = -I`.
      rcases order72_E9_sq_cases (φ e8e3) hF3 with h3 | h3 | ⟨θ3, h3⟩
      · right
        left
        have hφ : φ = order72_e9E8Neg100Action.comp order72_E8_shear12.toMonoidHom := by
          apply e8_hom_ext <;> simp [h1, h2, h3]
        exact ⟨(semidirectProductCongr_eq hφ).trans
          (semidirectProductCongrAut (φ := order72_e9E8Neg100Action) order72_E8_shear12)⟩
      · right
        left
        have hφ : φ = order72_e9E8Neg100Action.comp
            (order72_E8_shear13.toMonoidHom.comp order72_E8_shear12.toMonoidHom) := by
          apply e8_hom_ext <;> simp [h1, h2, h3]
        exact ⟨(semidirectProductCongr_eq hφ).trans
          (order72_e9_e8_congrAut2 order72_e9E8Neg100Action order72_E8_shear13
            order72_E8_shear12)⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ3).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_swap23.toMonoidHom.comp order72_E8_shear12.toMonoidHom) := by
          apply e8_hom_ext
          · change (MulAut.conj θ3) (φ e8e1) = _
            rw [h1, order72_E9_conj_negAut]
            simp
          · change (MulAut.conj θ3) (φ e8e2) = _
            rw [h2, order72_E9_conj_negAut]
            simp
          · change (MulAut.conj θ3) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ3).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut2 order72_e9E8V4Action order72_E8_swap23
              order72_E8_shear12))⟩
    · -- `F2` conjugate to the standard reflection.
      have hF3'2 : ((MulAut.conj θ2) (φ e8e3)) ^ 2 = 1 := by
        rw [← map_pow, hF3, map_one]
      have hcomm3' : Commute ((MulAut.conj θ2) (φ e8e3)) order72_E9_reflectAut := by
        rw [← h2]
        exact (c23.map (MulAut.conj θ2).toMonoidHom).symm
      rcases order72_E9_reflect_centralizer_sq_cases ((MulAut.conj θ2) (φ e8e3)) hF3'2
        hcomm3' with h3 | h3 | h3 | h3
      · right
        right
        right
        have hφ : (MulAut.conj θ2).toMonoidHom.comp φ = order72_e9E8V4Action := by
          apply e8_hom_ext
          · change (MulAut.conj θ2) (φ e8e1) = _
            rw [h1, order72_E9_conj_negAut]
            simp
          · change (MulAut.conj θ2) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ2) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ2).trans
          (semidirectProductCongr_eq hφ)⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ2).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp order72_E8_shear13.toMonoidHom := by
          apply e8_hom_ext
          · change (MulAut.conj θ2) (φ e8e1) = _
            rw [h1, order72_E9_conj_negAut]
            simp
          · change (MulAut.conj θ2) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ2) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ2).trans
          ((semidirectProductCongr_eq hφ).trans
            (semidirectProductCongrAut (φ := order72_e9E8V4Action) order72_E8_shear13))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ2).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp order72_E8_shear23.toMonoidHom := by
          apply e8_hom_ext
          · change (MulAut.conj θ2) (φ e8e1) = _
            rw [h1, order72_E9_conj_negAut]
            simp
          · change (MulAut.conj θ2) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ2) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ2).trans
          ((semidirectProductCongr_eq hφ).trans
            (semidirectProductCongrAut (φ := order72_e9E8V4Action) order72_E8_shear23))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ2).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_shear13.toMonoidHom.comp order72_E8_shear23.toMonoidHom) := by
          apply e8_hom_ext
          · change (MulAut.conj θ2) (φ e8e1) = _
            rw [h1, order72_E9_conj_negAut]
            simp
          · change (MulAut.conj θ2) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ2) (φ e8e3) = _
            rw [h3]
            simp [order72_E9_reflectAut_mul_negAut]
        exact ⟨(semidirectProductCongrConj (φ := φ) θ2).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut2 order72_e9E8V4Action order72_E8_shear13
              order72_E8_shear23))⟩
  · -- `F1` conjugate to the standard reflection.
    have hF2'2 : ((MulAut.conj θ1) (φ e8e2)) ^ 2 = 1 := by
      rw [← map_pow, hF2, map_one]
    have hcomm2' : Commute ((MulAut.conj θ1) (φ e8e2)) order72_E9_reflectAut := by
      rw [← h1]
      exact (c12.map (MulAut.conj θ1).toMonoidHom).symm
    have hF3'2 : ((MulAut.conj θ1) (φ e8e3)) ^ 2 = 1 := by
      rw [← map_pow, hF3, map_one]
    have hcomm3' : Commute ((MulAut.conj θ1) (φ e8e3)) order72_E9_reflectAut := by
      rw [← h1]
      exact (c13.map (MulAut.conj θ1).toMonoidHom).symm
    rcases order72_E9_reflect_centralizer_sq_cases ((MulAut.conj θ1) (φ e8e2)) hF2'2
      hcomm2' with h2 | h2 | h2 | h2
    · -- `F2' = 1`.
      rcases order72_E9_reflect_centralizer_sq_cases ((MulAut.conj θ1) (φ e8e3)) hF3'2
        hcomm3' with h3 | h3 | h3 | h3
      · right
        right
        left
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ = order72_e9E8Reflect100Action := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          (semidirectProductCongr_eq hφ)⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_swap12.toMonoidHom.comp order72_E8_swap23.toMonoidHom) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut2 order72_e9E8V4Action order72_E8_swap12
              order72_E8_swap23))⟩
      · right
        right
        left
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8Reflect100Action.comp order72_E8_shear13.toMonoidHom := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (semidirectProductCongrAut (φ := order72_e9E8Reflect100Action)
              order72_E8_shear13))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_swap12.toMonoidHom.comp
                (order72_E8_swap23.toMonoidHom.comp order72_E8_shear13.toMonoidHom)) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp [order72_E9_reflectAut_mul_negAut]
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut3 order72_e9E8V4Action order72_E8_swap12
              order72_E8_swap23 order72_E8_shear13))⟩
    · -- `F2' = -I`.
      rcases order72_E9_reflect_centralizer_sq_cases ((MulAut.conj θ1) (φ e8e3)) hF3'2
        hcomm3' with h3 | h3 | h3 | h3
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp order72_E8_swap12.toMonoidHom := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (semidirectProductCongrAut (φ := order72_e9E8V4Action) order72_E8_swap12))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_shear13.toMonoidHom.comp order72_E8_swap12.toMonoidHom) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut2 order72_e9E8V4Action order72_E8_shear13
              order72_E8_swap12))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_shear23.toMonoidHom.comp order72_E8_swap12.toMonoidHom) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut2 order72_e9E8V4Action order72_E8_shear23
              order72_E8_swap12))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_shear13.toMonoidHom.comp
                (order72_E8_shear23.toMonoidHom.comp order72_E8_swap12.toMonoidHom)) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp [order72_E9_reflectAut_mul_negAut]
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut3 order72_e9E8V4Action order72_E8_shear13
              order72_E8_shear23 order72_E8_swap12))⟩
    · -- `F2' = ` the standard reflection itself.
      rcases order72_E9_reflect_centralizer_sq_cases ((MulAut.conj θ1) (φ e8e3)) hF3'2
        hcomm3' with h3 | h3 | h3 | h3
      · right
        right
        left
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8Reflect100Action.comp order72_E8_shear12.toMonoidHom := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (semidirectProductCongrAut (φ := order72_e9E8Reflect100Action)
              order72_E8_shear12))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_swap12.toMonoidHom.comp
                (order72_E8_swap23.toMonoidHom.comp order72_E8_shear12.toMonoidHom)) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut3 order72_e9E8V4Action order72_E8_swap12
              order72_E8_swap23 order72_E8_shear12))⟩
      · right
        right
        left
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8Reflect100Action.comp
              (order72_E8_shear13.toMonoidHom.comp order72_E8_shear12.toMonoidHom) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut2 order72_e9E8Reflect100Action order72_E8_shear13
              order72_E8_shear12))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_swap12.toMonoidHom.comp
                (order72_E8_swap23.toMonoidHom.comp
                  (order72_E8_shear12.toMonoidHom.comp order72_E8_shear23.toMonoidHom))) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp [order72_E9_reflectAut_mul_negAut]
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut4 order72_e9E8V4Action order72_E8_swap12
              order72_E8_swap23 order72_E8_shear12 order72_E8_shear23))⟩
    · -- `F2' = diag(1,-1)`.
      rcases order72_E9_reflect_centralizer_sq_cases ((MulAut.conj θ1) (φ e8e3)) hF3'2
        hcomm3' with h3 | h3 | h3 | h3
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_swap12.toMonoidHom.comp order72_E8_shear12.toMonoidHom) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp [order72_E9_reflectAut_mul_negAut]
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut2 order72_e9E8V4Action order72_E8_swap12
              order72_E8_shear12))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_shear13.toMonoidHom.comp
                (order72_E8_swap12.toMonoidHom.comp order72_E8_shear12.toMonoidHom)) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp [order72_E9_reflectAut_mul_negAut]
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut3 order72_e9E8V4Action order72_E8_shear13
              order72_E8_swap12 order72_E8_shear12))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_shear23.toMonoidHom.comp
                (order72_E8_swap12.toMonoidHom.comp order72_E8_shear12.toMonoidHom)) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp [order72_E9_reflectAut_mul_negAut]
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut3 order72_e9E8V4Action order72_E8_shear23
              order72_E8_swap12 order72_E8_shear12))⟩
      · right
        right
        right
        have hφ : (MulAut.conj θ1).toMonoidHom.comp φ =
            order72_e9E8V4Action.comp
              (order72_E8_shear13.toMonoidHom.comp
                (order72_E8_shear23.toMonoidHom.comp
                  (order72_E8_swap12.toMonoidHom.comp order72_E8_shear12.toMonoidHom))) := by
          apply e8_hom_ext
          · change (MulAut.conj θ1) (φ e8e1) = _
            rw [h1]
            simp
          · change (MulAut.conj θ1) (φ e8e2) = _
            rw [h2]
            simp [order72_E9_reflectAut_mul_negAut]
          · change (MulAut.conj θ1) (φ e8e3) = _
            rw [h3]
            simp [order72_E9_reflectAut_mul_negAut]
        exact ⟨(semidirectProductCongrConj (φ := φ) θ1).trans
          ((semidirectProductCongr_eq hφ).trans
            (order72_e9_e8_congrAut4 order72_e9E8V4Action order72_E8_shear13
              order72_E8_shear23 order72_E8_swap12 order72_E8_shear12))⟩

/-- The `G`-level version of the `E9 ⋊ E8` classification. -/
theorem order72_e9_e8_branch_cases {G : Type*} [Group G]
    {φ : E8 →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ) :
    Nonempty (G ≃* ElemAbelianRep 3 × E8) ∨
    Nonempty (G ≃* order72_E9_E8_neg100) ∨
    Nonempty (G ≃* order72_E9_E8_reflect100) ∨
    Nonempty (G ≃* order72_E9_E8_v4) := by
  rcases order72_e9_e8_semidirect_cases φ with h | h | h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inl ⟨e.trans eh⟩)
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨e.trans eh⟩))

/-! ### The Sylow-`3`-normal branch with `E9 ⋊ C8`, `E9 ⋊ H2` and `E9 ⋊ E8` classified. -/

/-- The fully classified part of the Sylow-`3`-normal branch after solving the
`E9 ⋊ E8` cell: the previous solved cases together with the direct product and the
three `E9 ⋊ E8` representatives. -/
abbrev order72Sylow3NormalSolvedC9AllE9C8H2E8Cases (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9AllE9C8H2Cases G ∨
    Nonempty (G ≃* ElemAbelianRep 3 × E8) ∨
      Nonempty (G ≃* order72_E9_E8_neg100) ∨
        Nonempty (G ≃* order72_E9_E8_reflect100) ∨
          Nonempty (G ≃* order72_E9_E8_v4)

/-- The remaining action problems of the Sylow-`3`-normal branch: `E9 ⋊ H` with
`H ∈ {D4, Q8}`. -/
abbrev order72Sylow3NormalRemainingSemidirectCasesE9D4Q8 (G : Type*) [Group G] :
    Prop :=
  (∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ))

/-- The Sylow-`3`-normal branch with the `C9 ⋊ H`, `E9 ⋊ C8`, `E9 ⋊ H2` and `E9 ⋊ E8`
cells fully classified: the remaining cases are exactly the two `E9 ⋊ H` action
problems with `H ∈ {D4, Q8}`. -/
abbrev order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Done (G : Type*) [Group G] :
    Prop :=
  order72Sylow3NormalSolvedC9AllE9C8H2E8Cases G ∨
    order72Sylow3NormalRemainingSemidirectCasesE9D4Q8 G

private theorem order72PartialC9AllE9C8H2E8Done_of_h2_done {G : Type*} [Group G] :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2Done G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Done G := by
  intro hcases
  rcases hcases with hsolved | hrem
  · left
    left
    exact hsolved
  · rcases hrem with hE8 | hD4 | hQ8
    · obtain ⟨φ, ⟨e⟩⟩ := hE8
      rcases order72_e9_e8_branch_cases e with h0 | h1 | h2 | h3
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
        exact h3
    · right
      left
      exact hD4
    · right
      right
      exact hQ8

theorem order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_h2_e8_done
    {G : Type*} [Group G] :
    order72Sylow3NormalSemidirectCases G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Done G := by
  intro hcases
  exact order72PartialC9AllE9C8H2E8Done_of_h2_done
    (order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_h2_done hcases)

/-- The `n₃ = 1` branch with all `C9 ⋊ H`, `E9 ⋊ C8`, `E9 ⋊ H2` and `E9 ⋊ E8` cases
reduced to explicit representatives. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_h2_e8_done_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Done G :=
  order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_h2_e8_done
    (order72_semidirectProduct_standard_cases_of_sylow_three_normal hG hSyl)

/-- The `n₃ = 1` branch with all `C9 ⋊ H`, `E9 ⋊ C8`, `E9 ⋊ H2` and `E9 ⋊ E8` cases
reduced to explicit representatives. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_h2_e8_done_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Done G := by
  exact order72_partial_rep_cases_c9_all_e9_c8_h2_e8_done_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- Current top-level reduction: in the Sylow-`3`-normal branch every `C9 ⋊ H`,
`E9 ⋊ C8`, `E9 ⋊ H2` and `E9 ⋊ E8` case is now explicit; the remaining semidirect
action problems are `E9 ⋊ D4` and `E9 ⋊ Q8`. -/
theorem order72_partial_classification_refined_c9_all_e9_c8_h2_e8_done
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8H2E8Done G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl
      (order72_partial_rep_cases_c9_all_e9_c8_h2_e8_done_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)

end Smallgroups.UsefulTheorems
