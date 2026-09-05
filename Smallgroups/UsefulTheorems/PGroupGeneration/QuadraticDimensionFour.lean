/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticNormalForms4
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticPolarZeroClassification
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticRadicalReduction

/-! Witt reduction of four-dimensional quadratic forms over `F₂`. -/

namespace Smallgroups.UsefulTheorems.GF2Certificate

variable {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]

private theorem dimensionFour_f2_square (a : F2) : a * a = a := by
  fin_cases a <;> rfl

private theorem dimensionFour_f2_eq_one (a : F2) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

theorem singleSquarePlane_prod_zero_polar :
    (singleSquarePlane.prod (0 : QuadraticMap F2 QuadraticPlaneV F2)).polarBilin = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    QuadraticMap.prod_apply, singleSquarePlane_apply, QuadraticMap.zero_apply,
    Prod.fst_add, add_zero, LinearMap.zero_apply]
  rw [dimensionFour_f2_square, dimensionFour_f2_square, dimensionFour_f2_square]
  abel

theorem singleSquarePlane_prod_zero_ne_zero :
    singleSquarePlane.prod (0 : QuadraticMap F2 QuadraticPlaneV F2) ≠ 0 := by
  intro h
  have h' := congrArg (fun q : QuadraticMap F2 (QuadraticPlaneV × QuadraticPlaneV) F2 =>
    q ((1, 0), (0, 0))) h
  change (1 : F2) = 0 at h'
  exact one_ne_zero h'

/-- The zero form on any four-dimensional carrier is the first standard form. -/
theorem quadraticDimensionFour_zero (Q : QuadraticMap F2 V F2)
    (hdim : Module.finrank F2 V = 4) (hQ : Q = 0) :
    Q.Equivalent (quadraticFourNormalForm 0) := by
  let e : V ≃ₗ[F2] QuadraticPlaneV × QuadraticPlaneV :=
    LinearEquiv.ofFinrankEq V (QuadraticPlaneV × QuadraticPlaneV) (by
      simpa only [Module.finrank_prod, Module.finrank_self] using hdim)
  refine ⟨{ toLinearEquiv := e, map_app' := ?_ }⟩
  intro v
  simp [quadraticFourNormalForm, hQ]

/-- Nonzero polarization splits a four-dimensional space into two planes.
The only radical case requiring a further identification is supplied explicitly. -/
theorem quadraticDimensionFour_nonzeroPolar_of_absorption
    (habsorb : (anisotropicPlane.prod singleSquarePlane).Equivalent
      (hyperbolicPlane.prod singleSquarePlane))
    (Q : QuadraticMap F2 V F2) (hdim : Module.finrank F2 V = 4)
    (hB : Q.polarBilin ≠ 0) :
    ∃ o : Fin 7, Q.Equivalent (quadraticFourNormalForm o) := by
  classical
  have hex : ∃ x y : V, Q.polarBilin x y ≠ 0 := by
    by_contra hn
    apply hB
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    by_contra hxy
    exact hn ⟨x, y, hxy⟩
  obtain ⟨x, y, hxy'⟩ := hex
  have hxy : Q.polarBilin x y = 1 := dimensionFour_f2_eq_one _ hxy'
  let K := quadraticPlaneOrthogonal Q x y
  let R := Q.restrict K
  have hdK : Module.finrank F2 K = 2 := by
    rw [quadraticPlaneOrthogonal_finrank Q x y hxy, hdim]
  have he : Q.Equivalent ((binaryPlane (Q x) (Q y)).prod R) :=
    ⟨quadraticPlaneSplitIsometry Q x y hxy⟩
  rcases binaryPlane_equivalent_hyperbolic_or_anisotropic (Q x) (Q y) with hp | hp <;>
    rcases quadraticDimensionTwo_classification R hdK with hr | hr | hr | hr
  · exact ⟨2, he.trans (hp.prod hr)⟩
  · exact ⟨4, he.trans (hp.prod hr)⟩
  · exact ⟨5, he.trans (hp.prod hr)⟩
  · exact ⟨6, he.trans (hp.prod hr)⟩
  · exact ⟨3, he.trans (hp.prod hr)⟩
  · exact ⟨4, (he.trans (hp.prod hr)).trans habsorb⟩
  · exact ⟨6, (he.trans (hp.prod hr)).trans
      ⟨QuadraticMap.IsometryEquiv.prodComm anisotropicPlane hyperbolicPlane⟩⟩
  · exact ⟨5, (he.trans (hp.prod hr)).trans
      ⟨anisotropicDoubleEquivHyperbolicDouble⟩⟩

/-- Every four-dimensional quadratic form over `F₂` is equivalent to one of the
seven standard forms. The reduction splits off a plane whenever polarization is
nonzero and otherwise classifies the remaining linear functional. -/
theorem quadraticDimensionFour_classification (Q : QuadraticMap F2 V F2)
    (hdim : Module.finrank F2 V = 4) :
    ∃ o : Fin 7, Q.Equivalent (quadraticFourNormalForm o) := by
  classical
  by_cases hB : Q.polarBilin = 0
  · by_cases hQ : Q = 0
    · exact ⟨0, quadraticDimensionFour_zero Q hdim hQ⟩
    · refine ⟨1, ?_⟩
      change Q.Equivalent (singleSquarePlane.prod (0 : QuadraticMap F2 QuadraticPlaneV F2))
      exact quadraticPolarZero_equivalent_of_nonzero Q _ hB
        singleSquarePlane_prod_zero_polar hQ singleSquarePlane_prod_zero_ne_zero
        (by simpa only [Module.finrank_prod, Module.finrank_self] using hdim)
  · exact quadraticDimensionFour_nonzeroPolar_of_absorption
      anisotropicPlane_prod_singleSquare_equivalent Q hdim hB

end Smallgroups.UsefulTheorems.GF2Certificate
