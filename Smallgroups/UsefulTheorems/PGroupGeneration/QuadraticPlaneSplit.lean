/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.Tactic.Ring
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticInvariants

/-!
# Splitting off a nondegenerate quadratic plane over `F₂`

If the polar pairing of `x` and `y` is one, they span a nondegenerate plane.
Every vector has unique coordinates in that plane and its common orthogonal
complement. The equivalence below gives these coordinates explicitly, without a
dimension or finiteness assumption.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

variable {V : Type*} [AddCommGroup V] [Module F2 V]

private theorem quadraticPlane_polar_comm (Q : QuadraticMap F2 V F2) (x y : V) :
    Q.polarBilin x y = Q.polarBilin y x :=
  QuadraticMap.polar_comm Q x y

/-- The common orthogonal complement of two vectors under a quadratic polar form. -/
def quadraticPlaneOrthogonal (Q : QuadraticMap F2 V F2) (x y : V) : Submodule F2 V :=
  (Q.polarBilin x).ker ⊓ (Q.polarBilin y).ker

@[simp] theorem mem_quadraticPlaneOrthogonal (Q : QuadraticMap F2 V F2) (x y v : V) :
    v ∈ quadraticPlaneOrthogonal Q x y ↔
      Q.polarBilin x v = 0 ∧ Q.polarBilin y v = 0 :=
  Iff.rfl

/-- Subtract the two plane coordinates. Subtraction equals addition over `F₂`. -/
def quadraticPlaneRemainder (Q : QuadraticMap F2 V F2) (x y : V) : V →ₗ[F2] V where
  toFun v := v + Q.polarBilin v y • x + Q.polarBilin v x • y
  map_add' u v := by
    simp only [map_add, LinearMap.add_apply, add_smul]
    abel
  map_smul' a v := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_add, smul_smul,
      RingHom.id_apply]

@[simp] theorem quadraticPlaneRemainder_apply (Q : QuadraticMap F2 V F2) (x y v : V) :
    quadraticPlaneRemainder Q x y v =
      v + Q.polarBilin v y • x + Q.polarBilin v x • y :=
  rfl

/-- The explicit remainder lies in the common orthogonal complement. -/
theorem quadraticPlaneRemainder_mem (Q : QuadraticMap F2 V F2) (x y : V)
    (hxy : Q.polarBilin x y = 1) (v : V) :
    quadraticPlaneRemainder Q x y v ∈ quadraticPlaneOrthogonal Q x y := by
  have hyx : Q.polarBilin y x = 1 :=
    (quadraticPlane_polar_comm Q y x).trans hxy
  constructor
  · change Q.polarBilin x
      (v + Q.polarBilin v y • x + Q.polarBilin v x • y) = 0
    simp only [map_add, map_smul, smul_eq_mul, quadraticPolarBilin_self_eq_zero,
      hxy, mul_zero, mul_one, add_zero, quadraticPlane_polar_comm Q x v]
    exact ZModModule.add_self _
  · change Q.polarBilin y
      (v + Q.polarBilin v y • x + Q.polarBilin v x • y) = 0
    simp only [map_add, map_smul, smul_eq_mul, quadraticPolarBilin_self_eq_zero,
      hyx, mul_zero, mul_one, add_zero, quadraticPlane_polar_comm Q y v]
    exact ZModModule.add_self _

private theorem quadraticPlane_reconstruct_polar_y (Q : QuadraticMap F2 V F2) (x y : V)
    (hxy : Q.polarBilin x y = 1) (a b : F2) (k : quadraticPlaneOrthogonal Q x y) :
    Q.polarBilin (a • x + b • y + k.val) y = a := by
  have hky : Q.polarBilin k.val y = 0 :=
    (quadraticPlane_polar_comm Q k.val y).trans k.property.2
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hxy, quadraticPolarBilin_self_eq_zero, hky, mul_one, mul_zero, add_zero]

private theorem quadraticPlane_reconstruct_polar_x (Q : QuadraticMap F2 V F2) (x y : V)
    (hxy : Q.polarBilin x y = 1) (a b : F2) (k : quadraticPlaneOrthogonal Q x y) :
    Q.polarBilin (a • x + b • y + k.val) x = b := by
  have hyx : Q.polarBilin y x = 1 :=
    (quadraticPlane_polar_comm Q y x).trans hxy
  have hkx : Q.polarBilin k.val x = 0 :=
    (quadraticPlane_polar_comm Q k.val x).trans k.property.1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hyx, quadraticPolarBilin_self_eq_zero, hkx, mul_one, mul_zero, add_zero, zero_add]

/-- Explicit orthogonal plane decomposition. The first coordinates are
`B(v,y)` and `B(v,x)`, and the inverse reconstructs `a • x + b • y + k`. -/
def quadraticPlaneSplit (Q : QuadraticMap F2 V F2) (x y : V)
    (hxy : Q.polarBilin x y = 1) :
    V ≃ₗ[F2] (F2 × F2) × quadraticPlaneOrthogonal Q x y where
  toFun v :=
    ((Q.polarBilin v y, Q.polarBilin v x),
      ⟨quadraticPlaneRemainder Q x y v, quadraticPlaneRemainder_mem Q x y hxy v⟩)
  invFun z := z.1.1 • x + z.1.2 • y + z.2.val
  left_inv v := by
    change Q.polarBilin v y • x + Q.polarBilin v x • y +
      (v + Q.polarBilin v y • x + Q.polarBilin v x • y) = v
    calc
      _ = v + (Q.polarBilin v y • x + Q.polarBilin v y • x) +
          (Q.polarBilin v x • y + Q.polarBilin v x • y) := by abel
      _ = v := by simp only [ZModModule.add_self, add_zero]
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · exact quadraticPlane_reconstruct_polar_y Q x y hxy z.1.1 z.1.2 z.2
      · exact quadraticPlane_reconstruct_polar_x Q x y hxy z.1.1 z.1.2 z.2
    · apply Subtype.ext
      change quadraticPlaneRemainder Q x y (z.1.1 • x + z.1.2 • y + z.2.val) = z.2.val
      rw [quadraticPlaneRemainder_apply,
        quadraticPlane_reconstruct_polar_y Q x y hxy,
        quadraticPlane_reconstruct_polar_x Q x y hxy]
      calc
        _ = z.2.val + (z.1.1 • x + z.1.1 • x) + (z.1.2 • y + z.1.2 • y) := by abel
        _ = z.2.val := by simp only [ZModModule.add_self, add_zero]
  map_add' u v := by
    apply Prod.ext
    · apply Prod.ext <;> simp only [map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add]
    · apply Subtype.ext
      exact (quadraticPlaneRemainder Q x y).map_add u v
  map_smul' a v := by
    apply Prod.ext
    · apply Prod.ext <;>
        simp only [map_smul, LinearMap.smul_apply, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    · apply Subtype.ext
      exact (quadraticPlaneRemainder Q x y).map_smul a v

@[simp] theorem quadraticPlaneSplit_apply (Q : QuadraticMap F2 V F2) (x y : V)
    (hxy : Q.polarBilin x y = 1) (v : V) :
    quadraticPlaneSplit Q x y hxy v =
      ((Q.polarBilin v y, Q.polarBilin v x),
        ⟨quadraticPlaneRemainder Q x y v, quadraticPlaneRemainder_mem Q x y hxy v⟩) :=
  rfl

@[simp] theorem quadraticPlaneSplit_symm_apply (Q : QuadraticMap F2 V F2) (x y : V)
    (hxy : Q.polarBilin x y = 1) (z : (F2 × F2) × quadraticPlaneOrthogonal Q x y) :
    (quadraticPlaneSplit Q x y hxy).symm z = z.1.1 • x + z.1.2 • y + z.2.val :=
  rfl

private theorem quadraticPlane_map_add (Q : QuadraticMap F2 V F2) (u v : V) :
    Q (u + v) = Q u + Q v + Q.polarBilin u v := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  abel

/-- The quadratic form separates into its two-dimensional part and the restriction
to the orthogonal complement. -/
theorem quadraticPlaneSplit_map_symm (Q : QuadraticMap F2 V F2) (x y : V)
    (hxy : Q.polarBilin x y = 1) (a b : F2) (k : quadraticPlaneOrthogonal Q x y) :
    Q ((quadraticPlaneSplit Q x y hxy).symm ((a, b), k)) =
      Q x * a ^ 2 + a * b + Q y * b ^ 2 + Q k.val := by
  rw [quadraticPlaneSplit_symm_apply, quadraticPlane_map_add, quadraticPlane_map_add,
    Q.map_smul, Q.map_smul]
  have hxk : Q.polarBilin x k.val = 0 := k.property.1
  have hyk : Q.polarBilin y k.val = 0 := k.property.2
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hxy, hxk, hyk, mul_zero, mul_one, add_zero]
  ring

/-- The same decomposition expressed in the forward coordinates of an arbitrary vector. -/
theorem quadraticPlaneSplit_map (Q : QuadraticMap F2 V F2) (x y : V)
    (hxy : Q.polarBilin x y = 1) (v : V) :
    Q v = Q x * (Q.polarBilin v y) ^ 2 + Q.polarBilin v y * Q.polarBilin v x +
      Q y * (Q.polarBilin v x) ^ 2 + Q (quadraticPlaneRemainder Q x y v) := by
  have h := quadraticPlaneSplit_map_symm Q x y hxy
    (quadraticPlaneSplit Q x y hxy v).1.1
    (quadraticPlaneSplit Q x y hxy v).1.2
    (quadraticPlaneSplit Q x y hxy v).2
  simp only [Prod.eta, LinearEquiv.symm_apply_apply] at h
  simpa only [quadraticPlaneSplit_apply] using h

end Smallgroups.UsefulTheorems.GF2Certificate
