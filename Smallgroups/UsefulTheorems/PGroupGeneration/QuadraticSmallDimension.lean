/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticPlaneSplit
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticPlanes

/-!
# Small-dimensional quadratic spaces over `F₂`

The explicit plane decomposition gives the dimension drop used in Witt
reduction. In dimension two, a nonzero polar form leaves no orthogonal
remainder, and the space is hyperbolic or anisotropic. A zero polar form is
linear over `F₂` and has either zero or one essential coordinate.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

variable {V : Type*} [AddCommGroup V] [Module F2 V]

private theorem smallDimension_f2_square (a : F2) : a * a = a := by
  fin_cases a <;> rfl

private theorem smallDimension_f2_eq_one (a : F2) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

/-- A quadratic map with zero polarization is linear over `F₂`. -/
def quadraticLinearOfPolarZero (Q : QuadraticMap F2 V F2) (hB : Q.polarBilin = 0) :
    V →ₗ[F2] F2 where
  toFun := Q
  map_add' x y := by
    have h := congrArg (fun B : V →ₗ[F2] V →ₗ[F2] F2 => B x y) hB
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      LinearMap.zero_apply] at h
    rw [sub_sub] at h
    exact sub_eq_zero.mp h
  map_smul' a x := by
    rw [Q.map_smul, smallDimension_f2_square]
    rfl

@[simp] theorem quadraticLinearOfPolarZero_apply (Q : QuadraticMap F2 V F2)
    (hB : Q.polarBilin = 0) (v : V) : quadraticLinearOfPolarZero Q hB v = Q v := rfl

/-- The explicit plane coordinates respect the orthogonal sum of quadratic forms. -/
def quadraticPlaneSplitIsometry (Q : QuadraticMap F2 V F2) (x y : V)
    (hxy : Q.polarBilin x y = 1) :
    Q.IsometryEquiv ((binaryPlane (Q x) (Q y)).prod
      (Q.restrict (quadraticPlaneOrthogonal Q x y))) where
  toLinearEquiv := quadraticPlaneSplit Q x y hxy
  map_app' v := by
    change binaryPlane (Q x) (Q y) (quadraticPlaneSplit Q x y hxy v).1 +
      Q (quadraticPlaneSplit Q x y hxy v).2.val = Q v
    rw [quadraticPlaneSplit_apply]
    simpa only [binaryPlane_apply, pow_two] using (quadraticPlaneSplit_map Q x y hxy v).symm

/-- Splitting a nondegenerate plane removes exactly two dimensions. -/
theorem quadraticPlaneOrthogonal_finrank_add [FiniteDimensional F2 V]
    (Q : QuadraticMap F2 V F2) (x y : V) (hxy : Q.polarBilin x y = 1) :
    Module.finrank F2 V = 2 + Module.finrank F2 (quadraticPlaneOrthogonal Q x y) := by
  have h := (quadraticPlaneSplit Q x y hxy).finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self] using h

theorem quadraticPlaneOrthogonal_finrank [FiniteDimensional F2 V]
    (Q : QuadraticMap F2 V F2) (x y : V) (hxy : Q.polarBilin x y = 1) :
    Module.finrank F2 (quadraticPlaneOrthogonal Q x y) = Module.finrank F2 V - 2 := by
  rw [quadraticPlaneOrthogonal_finrank_add Q x y hxy]
  omega

/-- In dimension two there is no orthogonal remainder after a plane split. -/
noncomputable def quadraticDimensionTwoBinaryIsometry [FiniteDimensional F2 V]
    (Q : QuadraticMap F2 V F2) (hdim : Module.finrank F2 V = 2) (x y : V)
    (hxy : Q.polarBilin x y = 1) : Q.IsometryEquiv (binaryPlane (Q x) (Q y)) := by
  have hk : Module.finrank F2 (quadraticPlaneOrthogonal Q x y) = 0 := by
    rw [quadraticPlaneOrthogonal_finrank Q x y hxy, hdim]
  letI : Subsingleton (quadraticPlaneOrthogonal Q x y) :=
    (Module.finrank_zero_iff).mp hk
  letI : Unique (quadraticPlaneOrthogonal Q x y) :=
    ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  refine
    { toLinearEquiv := (quadraticPlaneSplit Q x y hxy).trans
        (LinearEquiv.prodUnique (R := F2) (M := QuadraticPlaneV)
          (M₂ := quadraticPlaneOrthogonal Q x y))
      map_app' := ?_ }
  intro v
  have hr : quadraticPlaneRemainder Q x y v = 0 := by
    exact congrArg Subtype.val (Subsingleton.elim (quadraticPlaneSplit Q x y hxy v).2 0)
  have h := quadraticPlaneSplit_map Q x y hxy v
  rw [hr, Q.map_zero, add_zero] at h
  change binaryPlane (Q x) (Q y) (quadraticPlaneSplit Q x y hxy v).1 = Q v
  rw [quadraticPlaneSplit_apply]
  simpa only [binaryPlane_apply, pow_two] using h.symm

/-- A standard plane with one essential square coordinate. -/
def singleSquarePlane : QuadraticMap F2 QuadraticPlaneV F2 :=
  QuadraticMap.linMulLin (LinearMap.fst F2 F2 F2) (LinearMap.fst F2 F2 F2)

@[simp] theorem singleSquarePlane_apply (v : QuadraticPlaneV) :
    singleSquarePlane v = v.1 * v.1 := rfl

private theorem quadraticPolarZero_plane_formula (Q : QuadraticMap F2 QuadraticPlaneV F2)
    (hB : Q.polarBilin = 0) (v : QuadraticPlaneV) :
    Q v = Q (1, 0) * v.1 + Q (0, 1) * v.2 := by
  let l := quadraticLinearOfPolarZero Q hB
  have hv : v = v.1 • ((1, 0) : QuadraticPlaneV) + v.2 • ((0, 1) : QuadraticPlaneV) := by
    ext <;> simp
  change l v = l (1, 0) * v.1 + l (0, 1) * v.2
  conv_lhs => rw [hv, l.map_add, l.map_smul, l.map_smul]
  simp only [smul_eq_mul]
  ring

/-- A two-dimensional form with zero polarization is zero or a single square. -/
theorem quadraticPolarZero_plane_classification (Q : QuadraticMap F2 QuadraticPlaneV F2)
    (hB : Q.polarBilin = 0) :
    Q.Equivalent (0 : QuadraticMap F2 QuadraticPlaneV F2) ∨ Q.Equivalent singleSquarePlane := by
  generalize ha : Q (1, 0) = a
  generalize hb : Q (0, 1) = b
  have hform (v : QuadraticPlaneV) : Q v = a * v.1 + b * v.2 := by
    rw [quadraticPolarZero_plane_formula Q hB, ha, hb]
  fin_cases a <;> fin_cases b
  · change ∀ v, Q v = (0 : F2) * v.1 + (0 : F2) * v.2 at hform
    left
    exact ⟨{ toLinearEquiv := LinearEquiv.refl F2 QuadraticPlaneV
             map_app' := fun v => by simp [hform] }⟩
  · change ∀ v, Q v = (0 : F2) * v.1 + (1 : F2) * v.2 at hform
    right
    refine ⟨{ toLinearEquiv := LinearEquiv.prodComm F2 F2 F2
              map_app' := ?_ }⟩
    intro v
    change v.2 * v.2 = Q v
    simp [hform, smallDimension_f2_square]
  · change ∀ v, Q v = (1 : F2) * v.1 + (0 : F2) * v.2 at hform
    right
    refine ⟨{ toLinearEquiv := LinearEquiv.refl F2 QuadraticPlaneV
              map_app' := ?_ }⟩
    intro v
    change v.1 * v.1 = Q v
    simp [hform, smallDimension_f2_square]
  · change ∀ v, Q v = (1 : F2) * v.1 + (1 : F2) * v.2 at hform
    right
    refine ⟨{ toLinearEquiv := quadraticPlaneFirstShear
              map_app' := ?_ }⟩
    intro v
    change (v.1 + v.2) * (v.1 + v.2) = Q v
    simp [hform, smallDimension_f2_square]

/-- The zero-polar part of the two-dimensional classification, on any carrier. -/
theorem quadraticDimensionTwo_zeroPolar_classification [FiniteDimensional F2 V]
    (Q : QuadraticMap F2 V F2) (hdim : Module.finrank F2 V = 2) (hB : Q.polarBilin = 0) :
    Q.Equivalent (0 : QuadraticMap F2 QuadraticPlaneV F2) ∨ Q.Equivalent singleSquarePlane := by
  let e : V ≃ₗ[F2] QuadraticPlaneV := LinearEquiv.ofFinrankEq V QuadraticPlaneV (by
    simpa only [Module.finrank_prod, Module.finrank_self] using hdim)
  let Q' := Q.comp e.symm.toLinearMap
  have hB' : Q'.polarBilin = 0 := by
    change (Q.comp e.symm.toLinearMap).polarBilin = 0
    rw [QuadraticMap.polarBilin_comp, hB]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl
  have he : Q.Equivalent Q' := ⟨QuadraticMap.isometryEquivOfCompLinearEquiv Q e.symm⟩
  rcases quadraticPolarZero_plane_classification Q' hB' with h | h
  · exact Or.inl (he.trans h)
  · exact Or.inr (he.trans h)

/-- Every two-dimensional quadratic space over `F₂` is one of four standard forms. -/
theorem quadraticDimensionTwo_classification [FiniteDimensional F2 V]
    (Q : QuadraticMap F2 V F2) (hdim : Module.finrank F2 V = 2) :
    Q.Equivalent (0 : QuadraticMap F2 QuadraticPlaneV F2) ∨
      Q.Equivalent singleSquarePlane ∨ Q.Equivalent hyperbolicPlane ∨
      Q.Equivalent anisotropicPlane := by
  classical
  by_cases hB : Q.polarBilin = 0
  · rcases quadraticDimensionTwo_zeroPolar_classification Q hdim hB with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hex : ∃ x y : V, Q.polarBilin x y ≠ 0 := by
      by_contra hn
      apply hB
      ext x y
      by_contra hxy
      exact hn ⟨x, y, hxy⟩
    obtain ⟨x, y, hxy⟩ := hex
    have he : Q.Equivalent (binaryPlane (Q x) (Q y)) :=
      ⟨quadraticDimensionTwoBinaryIsometry Q hdim x y (smallDimension_f2_eq_one _ hxy)⟩
    rcases binaryPlane_equivalent_hyperbolic_or_anisotropic (Q x) (Q y) with h | h
    · exact Or.inr (Or.inr (Or.inl (he.trans h)))
    · exact Or.inr (Or.inr (Or.inr (he.trans h)))

end Smallgroups.UsefulTheorems.GF2Certificate
