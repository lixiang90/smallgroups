/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.Tactic.Ring
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticInvariants

/-!
# The two quadratic planes over `F₂`

The hyperbolic plane has square form `xy`; the anisotropic plane has square form
`x² + xy + y²`.  The orthogonal sum of two anisotropic planes is isometric to the
orthogonal sum of two hyperbolic planes.  The displayed change of coordinates is
checked by ordinary ring identities in characteristic two.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

private theorem f2_two : (2 : F2) = 0 := rfl
private theorem f2_three : (3 : F2) = 1 := rfl
private theorem f2_four : (4 : F2) = 0 := rfl
private theorem f2_six : (6 : F2) = 0 := rfl
private theorem f2_nine : (9 : F2) = 1 := rfl

attribute [local simp] f2_two f2_three f2_four f2_six f2_nine

private theorem f2_eq_one_of_ne_zero (a : F2) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

abbrev QuadraticPlaneV := F2 × F2

/-- The hyperbolic quadratic plane over `F₂`. -/
def hyperbolicPlane : QuadraticMap F2 QuadraticPlaneV F2 :=
  QuadraticMap.linMulLin (LinearMap.fst F2 F2 F2) (LinearMap.snd F2 F2 F2)

/-- The anisotropic quadratic plane over `F₂`. -/
def anisotropicPlane : QuadraticMap F2 QuadraticPlaneV F2 :=
  QuadraticMap.linMulLin (LinearMap.fst F2 F2 F2) (LinearMap.fst F2 F2 F2) +
    hyperbolicPlane +
    QuadraticMap.linMulLin (LinearMap.snd F2 F2 F2) (LinearMap.snd F2 F2 F2)

@[simp] theorem hyperbolicPlane_apply (x : QuadraticPlaneV) :
    hyperbolicPlane x = x.1 * x.2 := rfl

@[simp] theorem anisotropicPlane_apply (x : QuadraticPlaneV) :
    anisotropicPlane x = x.1 * x.1 + x.1 * x.2 + x.2 * x.2 := rfl

/-- The general binary quadratic form whose polar pairing on the standard basis is one. -/
def binaryPlane (a b : F2) : QuadraticMap F2 QuadraticPlaneV F2 :=
  a • QuadraticMap.linMulLin (LinearMap.fst F2 F2 F2) (LinearMap.fst F2 F2 F2) +
    hyperbolicPlane +
    b • QuadraticMap.linMulLin (LinearMap.snd F2 F2 F2) (LinearMap.snd F2 F2 F2)

@[simp] theorem binaryPlane_apply (a b : F2) (x : QuadraticPlaneV) :
    binaryPlane a b x = a * (x.1 * x.1) + x.1 * x.2 + b * (x.2 * x.2) := rfl

/-- Add the second coordinate to the first. -/
def quadraticPlaneFirstShear : QuadraticPlaneV ≃ₗ[F2] QuadraticPlaneV where
  toFun x := (x.1 + x.2, x.2)
  invFun x := (x.1 + x.2, x.2)
  left_inv x := by ext <;> first | rfl | (dsimp; ring_nf; simp)
  right_inv x := by ext <;> first | rfl | (dsimp; ring_nf; simp)
  map_add' x y := by ext <;> first | rfl | (dsimp; ring)
  map_smul' a x := by ext <;> first | rfl | (dsimp; ring)

/-- Add the first coordinate to the second. -/
def quadraticPlaneSecondShear : QuadraticPlaneV ≃ₗ[F2] QuadraticPlaneV where
  toFun x := (x.1, x.1 + x.2)
  invFun x := (x.1, x.1 + x.2)
  left_inv x := by ext <;> first | rfl | (dsimp; ring_nf; simp)
  right_inv x := by ext <;> first | rfl | (dsimp; ring_nf; simp)
  map_add' x y := by ext <;> first | rfl | (dsimp; ring)
  map_smul' a x := by ext <;> first | rfl | (dsimp; ring)

private def binaryZeroZeroEquivHyperbolic :
    (binaryPlane 0 0).IsometryEquiv hyperbolicPlane where
  toLinearEquiv := LinearEquiv.refl F2 QuadraticPlaneV
  map_app' x := by simp

private def binaryZeroOneEquivHyperbolic :
    (binaryPlane 0 1).IsometryEquiv hyperbolicPlane where
  toLinearEquiv := quadraticPlaneFirstShear
  map_app' x := by
    change (x.1 + x.2) * x.2 = 0 * (x.1 * x.1) + x.1 * x.2 + 1 * (x.2 * x.2)
    ring

private def binaryOneZeroEquivHyperbolic :
    (binaryPlane 1 0).IsometryEquiv hyperbolicPlane where
  toLinearEquiv := quadraticPlaneSecondShear
  map_app' x := by
    change x.1 * (x.1 + x.2) = 1 * (x.1 * x.1) + x.1 * x.2 + 0 * (x.2 * x.2)
    ring

private def binaryOneOneEquivAnisotropic :
    (binaryPlane 1 1).IsometryEquiv anisotropicPlane where
  toLinearEquiv := LinearEquiv.refl F2 QuadraticPlaneV
  map_app' x := by simp

/-- A binary form with zero product of diagonal coefficients is hyperbolic. -/
def binaryPlaneEquivHyperbolic (a b : F2) (hab : a * b = 0) :
    (binaryPlane a b).IsometryEquiv hyperbolicPlane := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      exact binaryZeroZeroEquivHyperbolic
    · have hb' := f2_eq_one_of_ne_zero b hb
      subst b
      exact binaryZeroOneEquivHyperbolic
  · have ha' := f2_eq_one_of_ne_zero a ha
    subst a
    have hb : b = 0 := by simpa using hab
    subst b
    exact binaryOneZeroEquivHyperbolic

/-- A binary form with nonzero product of diagonal coefficients is anisotropic. -/
def binaryPlaneEquivAnisotropic (a b : F2) (hab : a * b ≠ 0) :
    (binaryPlane a b).IsometryEquiv anisotropicPlane := by
  have ha : a ≠ 0 := by
    intro h
    apply hab
    simp [h]
  have hb : b ≠ 0 := by
    intro h
    apply hab
    simp [h]
  have ha' := f2_eq_one_of_ne_zero a ha
  have hb' := f2_eq_one_of_ne_zero b hb
  subst a
  subst b
  exact binaryOneOneEquivAnisotropic

/-- Every binary form with polar coefficient one has one of the two standard forms. -/
theorem binaryPlane_equivalent_hyperbolic_or_anisotropic (a b : F2) :
    (binaryPlane a b).Equivalent hyperbolicPlane ∨
      (binaryPlane a b).Equivalent anisotropicPlane := by
  by_cases hab : a * b = 0
  · exact Or.inl ⟨binaryPlaneEquivHyperbolic a b hab⟩
  · exact Or.inr ⟨binaryPlaneEquivAnisotropic a b hab⟩

/-- The orthogonal sum of two copies of a quadratic plane. -/
def quadraticPlaneDouble (Q : QuadraticMap F2 QuadraticPlaneV F2) :
    QuadraticMap F2 (QuadraticPlaneV × QuadraticPlaneV) F2 :=
  Q.comp (LinearMap.fst F2 QuadraticPlaneV QuadraticPlaneV) +
    Q.comp (LinearMap.snd F2 QuadraticPlaneV QuadraticPlaneV)

@[simp] theorem quadraticPlaneDouble_apply (Q : QuadraticMap F2 QuadraticPlaneV F2)
    (x : QuadraticPlaneV × QuadraticPlaneV) :
    quadraticPlaneDouble Q x = Q x.1 + Q x.2 := rfl

/-- The four columns are `(1,0,1,0)`, `(0,1,1,0)`, `(1,1,0,1)`, `(1,1,1,1)`. -/
def doublePlaneChange :
    (QuadraticPlaneV × QuadraticPlaneV) ≃ₗ[F2] (QuadraticPlaneV × QuadraticPlaneV) where
  toFun x := ((x.1.1 + x.2.1 + x.2.2, x.1.2 + x.2.1 + x.2.2),
    (x.1.1 + x.1.2 + x.2.2, x.2.1 + x.2.2))
  invFun y := ((y.1.1 + y.2.2, y.1.2 + y.2.2),
    (y.1.1 + y.1.2 + y.2.1 + y.2.2, y.1.1 + y.1.2 + y.2.1))
  left_inv x := by ext <;> dsimp <;> ring_nf <;> simp
  right_inv x := by ext <;> dsimp <;> ring_nf <;> simp
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' a x := by ext <;> dsimp <;> ring

/-- Two hyperbolic planes and two anisotropic planes are isometric. -/
def hyperbolicDoubleEquivAnisotropicDouble :
    (quadraticPlaneDouble hyperbolicPlane).IsometryEquiv
      (quadraticPlaneDouble anisotropicPlane) where
  toLinearEquiv := doublePlaneChange
  map_app' x := by
    simp only [quadraticPlaneDouble_apply, hyperbolicPlane_apply, anisotropicPlane_apply]
    change (x.1.1 + x.2.1 + x.2.2) * (x.1.1 + x.2.1 + x.2.2) +
        (x.1.1 + x.2.1 + x.2.2) * (x.1.2 + x.2.1 + x.2.2) +
        (x.1.2 + x.2.1 + x.2.2) * (x.1.2 + x.2.1 + x.2.2) +
        ((x.1.1 + x.1.2 + x.2.2) * (x.1.1 + x.1.2 + x.2.2) +
          (x.1.1 + x.1.2 + x.2.2) * (x.2.1 + x.2.2) +
          (x.2.1 + x.2.2) * (x.2.1 + x.2.2)) =
      x.1.1 * x.1.2 + x.2.1 * x.2.2
    ring_nf
    simp

/-- The characteristic-two cancellation `A ⊥ A ≃ H ⊥ H`. -/
def anisotropicDoubleEquivHyperbolicDouble :
    (quadraticPlaneDouble anisotropicPlane).IsometryEquiv
      (quadraticPlaneDouble hyperbolicPlane) :=
  hyperbolicDoubleEquivAnisotropicDouble.symm

end Smallgroups.UsefulTheorems.GF2Certificate
