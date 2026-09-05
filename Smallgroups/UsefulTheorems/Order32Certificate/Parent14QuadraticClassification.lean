/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Parent14QuadraticRepresentatives
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticDimensionFour
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticCocycleSplitting

/-!
# Structural classification of Parent 14 central extensions

Every quadratic space of dimension four over `F₂` has one of seven normal forms.
The checked coordinate changes identify them with the existing Parent 14
representatives. Equality of square quadratic forms up to linear equivalence
gives an isomorphism of central extensions by the cocycle splitting theorem.
No orbit forest or enumeration of the 1024 cohomology classes is used here.
-/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

/-- The structural seven-form classification on the original Parent 14 coordinates. -/
theorem parent14_quadratic_classification (Q : QuadraticMap F2 Parent14V F2) :
    ∃ o : Fin 7, Q.Equivalent
      (parent14Quadratic (parent14QuadraticRepresentativeCoeff o)) := by
  obtain ⟨o, ho⟩ := quadraticDimensionFour_classification Q (by
    simp [Parent14V])
  exact ⟨o, ho.trans ⟨parent14QuadraticRepresentativeIsometry o⟩⟩

/-- Any central extension of Parent 14 is one of the seven representatives,
by characteristic-two quadratic-space classification. -/
theorem parent14_extension_reduces_to_seven_structural
    (f : Order16Table.Q parent14Table → Order16Table.Q parent14Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 7, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP14SelectedCocycle o) (orbitP14SelectedCocycle_consistent o)) := by
  let fV : Multiplicative Parent14V → Multiplicative Parent14V → F2 :=
    fun x y => f (parent14VectorMulEquiv.symm x) (parent14VectorMulEquiv.symm y)
  let hfV : IsCentralCocycle fV := hf.comp parent14VectorMulEquiv.symm.toMonoidHom
  obtain ⟨o, ho⟩ := parent14_quadratic_classification (cocycleQuadratic fV hfV)
  obtain ⟨e⟩ := nonempty_cocycleGroup_mulEquiv_of_cocycleQuadratic_equivalent
    fV (parent14VectorCocycle (parent14QuadraticRepresentativeCoeff o)) hfV
    (parent14VectorCocycle_consistent _) ho
  refine ⟨o, ⟨?_⟩⟩
  exact (CocycleGroup.congrRight hf parent14VectorMulEquiv.symm).symm.trans
    (e.trans (CocycleGroup.congrRight (orbitP14SelectedCocycle_consistent o)
      parent14VectorMulEquiv.symm))

end Smallgroups.UsefulTheorems.Order32Certificate
