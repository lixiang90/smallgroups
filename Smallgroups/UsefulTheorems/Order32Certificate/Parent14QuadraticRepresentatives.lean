/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Parent14QuadraticBasics
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticNormalForms4Distinct

/-!
# Coordinates for the seven Parent 14 quadratic representatives

The four columns of each coordinate map identify a standard four-dimensional
quadratic form with one of the seven existing cocycles. Only these seven small
coordinate changes are checked by finite computation; classification of arbitrary
quadratic spaces is supplied by the structural dimension-four theorem.
-/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

/-- Columns sending standard plane coordinates to the original Parent 14 coordinates. -/
def parent14QuadraticColumns : Fin 7 → Fin 4 → ℕ :=
  ![![1, 2, 4, 8], ![4, 1, 2, 12], ![2, 4, 1, 14], ![2, 4, 1, 14],
    ![1, 4, 2, 15], ![1, 2, 7, 15], ![7, 9, 1, 4]]

/-- The linear map with the displayed four binary columns. -/
def parent14QuadraticCoordinateMap (o : Fin 7) :
    (QuadraticPlaneV × QuadraticPlaneV) →ₗ[F2] Parent14V where
  toFun v := v.1.1 • coeffMask 4 (parent14QuadraticColumns o 0) +
    v.1.2 • coeffMask 4 (parent14QuadraticColumns o 1) +
    v.2.1 • coeffMask 4 (parent14QuadraticColumns o 2) +
    v.2.2 • coeffMask 4 (parent14QuadraticColumns o 3)
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' a v := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_add, smul_smul,
      RingHom.id_apply, smul_eq_mul]

/-- Each of the seven displayed matrices is invertible over `F₂`. -/
theorem parent14QuadraticCoordinateMap_bijective (o : Fin 7) :
    Function.Bijective (parent14QuadraticCoordinateMap o) := by
  fin_cases o <;> decide +kernel

/-- The kernel verifies the quadratic identity on the sixteen vectors of each form. -/
theorem parent14QuadraticCoordinateMap_isometry (o : Fin 7) :
    ∀ v : QuadraticPlaneV × QuadraticPlaneV,
      parent14Quadratic (parent14QuadraticRepresentativeCoeff o)
        (parent14QuadraticCoordinateMap o v) = quadraticFourNormalForm o v := by
  fin_cases o <;> decide +kernel

/-- Each standard form is isometric to its original cocycle representative. -/
noncomputable def parent14QuadraticRepresentativeIsometry (o : Fin 7) :
    (quadraticFourNormalForm o).IsometryEquiv
      (parent14Quadratic (parent14QuadraticRepresentativeCoeff o)) where
  toLinearEquiv := LinearEquiv.ofBijective (parent14QuadraticCoordinateMap o)
    (parent14QuadraticCoordinateMap_bijective o)
  map_app' := parent14QuadraticCoordinateMap_isometry o

/-- The seven original representatives have pairwise inequivalent square forms. -/
theorem parent14QuadraticRepresentative_equivalent_iff (o p : Fin 7) :
    (parent14Quadratic (parent14QuadraticRepresentativeCoeff o)).Equivalent
      (parent14Quadratic (parent14QuadraticRepresentativeCoeff p)) ↔ o = p := by
  constructor
  · intro h
    apply (quadraticFourNormalForm_equivalent_iff o p).mp
    exact (QuadraticMap.Equivalent.trans ⟨parent14QuadraticRepresentativeIsometry o⟩ h).trans
      ⟨(parent14QuadraticRepresentativeIsometry p).symm⟩
  · rintro rfl
    exact ⟨QuadraticMap.IsometryEquiv.refl _⟩

end Smallgroups.UsefulTheorems.Order32Certificate
