/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticSmallDimension

/-!
# Absorbing binary square coefficients into the polar radical

If a quadratic space has a vector `t` in its polar kernel with `Q t = 1`,
the change `(x,y,w) ↦ (x,y,w + (a*x+b*y) • t)` absorbs both diagonal
coefficients of an orthogonal binary plane.  This identifies the hyperbolic
and anisotropic plane summands whenever the remaining radical has a nonzero
square function.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

variable {V : Type*} [AddCommGroup V] [Module F2 V]

private theorem radical_f2_mul_self (a : F2) : a * a = a := by
  fin_cases a <;> rfl

/-- Shear a complementary vector by a prescribed vector using the two plane coordinates. -/
def quadraticRadicalShear (a b : F2) (t : V) :
    (QuadraticPlaneV × V) ≃ₗ[F2] (QuadraticPlaneV × V) where
  toFun v := (v.1, v.2 + (a * v.1.1 + b * v.1.2) • t)
  invFun v := (v.1, v.2 + (a * v.1.1 + b * v.1.2) • t)
  left_inv v := by
    refine Prod.ext rfl ?_
    change (v.2 + (a * v.1.1 + b * v.1.2) • t) +
      (a * v.1.1 + b * v.1.2) • t = v.2
    rw [add_assoc, ZModModule.add_self, add_zero]
  right_inv v := by
    refine Prod.ext rfl ?_
    change (v.2 + (a * v.1.1 + b * v.1.2) • t) +
      (a * v.1.1 + b * v.1.2) • t = v.2
    rw [add_assoc, ZModModule.add_self, add_zero]
  map_add' u v := by
    refine Prod.ext rfl ?_
    change (u.2 + v.2) +
        (a * (u.1.1 + v.1.1) + b * (u.1.2 + v.1.2)) • t =
      (u.2 + (a * u.1.1 + b * u.1.2) • t) +
        (v.2 + (a * v.1.1 + b * v.1.2) • t)
    have hc : a * (u.1.1 + v.1.1) + b * (u.1.2 + v.1.2) =
        (a * u.1.1 + b * u.1.2) + (a * v.1.1 + b * v.1.2) := by ring
    rw [hc, add_smul]
    abel
  map_smul' c v := by
    refine Prod.ext rfl ?_
    change c • v.2 + (a * (c * v.1.1) + b * (c * v.1.2)) • t =
      c • (v.2 + (a * v.1.1 + b * v.1.2) • t)
    rw [smul_add, smul_smul]
    have hc : a * (c * v.1.1) + b * (c * v.1.2) =
        c * (a * v.1.1 + b * v.1.2) := by ring
    rw [hc]

@[simp] theorem quadraticRadicalShear_apply (a b : F2) (t : V)
    (v : QuadraticPlaneV × V) :
    quadraticRadicalShear a b t v = (v.1, v.2 + (a * v.1.1 + b * v.1.2) • t) :=
  rfl

/-- Shifting by a polar-kernel vector of square one adds the scalar square. -/
theorem quadraticRadicalShift_map (Q : QuadraticMap F2 V F2) (t : V)
    (htker : t ∈ Q.polarBilin.ker) (ht : Q t = 1) (c : F2) (v : V) :
    Q (v + c • t) = Q v + c * c := by
  have htv : Q.polarBilin t v = 0 := LinearMap.congr_fun htker v
  have hvt : Q.polarBilin v t = 0 := (QuadraticMap.polar_comm Q v t).trans htv
  have hp : QuadraticMap.polar Q v (c • t) = 0 := by
    change Q.polarBilin v (c • t) = 0
    rw [map_smul, hvt, smul_zero]
  rw [QuadraticMap.map_add Q v (c • t), Q.map_smul, hp, ht]
  simp only [smul_eq_mul, mul_one, add_zero]

/-- Nonzero square on the polar radical absorbs both binary diagonal coefficients. -/
def binaryPlaneRadicalAbsorption (Q : QuadraticMap F2 V F2) (t : V)
    (htker : t ∈ Q.polarBilin.ker) (ht : Q t = 1) (a b : F2) :
    ((binaryPlane a b).prod Q).IsometryEquiv (hyperbolicPlane.prod Q) where
  toLinearEquiv := quadraticRadicalShear a b t
  map_app' v := by
    change hyperbolicPlane v.1 + Q (v.2 + (a * v.1.1 + b * v.1.2) • t) =
      binaryPlane a b v.1 + Q v.2
    rw [quadraticRadicalShift_map Q t htker ht]
    simp only [hyperbolicPlane_apply, binaryPlane_apply, radical_f2_mul_self]
    ring

/-- Specialization to a one-dimensional square summand. -/
def binaryPlaneWithSquareEquivHyperbolicWithSquare (a b : F2) :
    ((binaryPlane a b).prod (QuadraticMap.sq : QuadraticMap F2 F2 F2)).IsometryEquiv
      (hyperbolicPlane.prod (QuadraticMap.sq : QuadraticMap F2 F2 F2)) := by
  apply binaryPlaneRadicalAbsorption _ (1 : F2) ?_ ?_ a b
  · apply LinearMap.ext
    intro x
    change (1 + x) * (1 + x) - 1 * 1 - x * x = 0
    simp only [radical_f2_mul_self]
    abel
  · rfl

/-- In dimension four, a nonzero radical square identifies the two plane choices. -/
def anisotropicPlaneProdSingleSquareEquiv :
    (anisotropicPlane.prod singleSquarePlane).IsometryEquiv
      (hyperbolicPlane.prod singleSquarePlane) := by
  have htker : (1, 0) ∈ singleSquarePlane.polarBilin.ker := by
    apply LinearMap.ext
    intro x
    change (1 + x.1) * (1 + x.1) - 1 * 1 - x.1 * x.1 = 0
    simp only [radical_f2_mul_self]
    abel
  have hbinary : binaryPlane 1 1 = anisotropicPlane := by
    ext x
    simp
  simpa only [hbinary] using
    binaryPlaneRadicalAbsorption singleSquarePlane (1, 0) htker rfl 1 1

theorem anisotropicPlane_prod_singleSquare_equivalent :
    (anisotropicPlane.prod singleSquarePlane).Equivalent
      (hyperbolicPlane.prod singleSquarePlane) :=
  ⟨anisotropicPlaneProdSingleSquareEquiv⟩

end Smallgroups.UsefulTheorems.GF2Certificate
