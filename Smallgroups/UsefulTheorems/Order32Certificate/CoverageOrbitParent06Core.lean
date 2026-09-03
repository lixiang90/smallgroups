/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Data

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 6. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP6_hbasis_cocycle (i : Fin 2) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent6Table (twoMask (coverageP6HBasis i))) := by
  fin_cases i <;> decide +kernel

def orbitP6AutCertificate (g : Fin 4) : Prop :=
  (∀ a : Fin 16, orbitP6AutInvPerm g (orbitP6AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP6AutPerm g (orbitP6AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP6AutPerm g (parent6Table.mul a b) =
    parent6Table.mul (orbitP6AutPerm g a) (orbitP6AutPerm g b))

theorem orbitP6_aut_certificate : ∀ g : Fin 4, orbitP6AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP6AutCertificate <;> decide +kernel

def orbitP6Aut (g : Fin 4) :
    Order16Table.Q parent6Table ≃* Order16Table.Q parent6Table where
  toFun x := ⟨orbitP6AutPerm g x.val⟩
  invFun x := ⟨orbitP6AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP6_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP6_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP6_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP6_action_linear (g : Fin 4) :
    (Order16Table.precomposeTwoLinear parent6Table (orbitP6Aut g)).comp
        ((Order16Table.decodeTwoLinear parent6Table).comp
          (synthesizeTwo coverageP6HBasis)) =
      (Order16Table.centralCoboundaryLinear parent6Table).comp
          (Order16Table.orbitCorrection parent6Table
            (orbitP6CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent6Table).comp
          ((synthesizeTwo coverageP6HBasis).comp
            (Order16Table.orbitAction (orbitP6ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 2)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP6SelectedCocycle (o : Fin 4) :=
  Order16Table.hCocycle parent6Table coverageP6HBasis
    (coeffMask 2 (orbitP6RepresentativeMask o))
theorem orbitP6SelectedCocycle_consistent (o : Fin 4) :
    IsCentralCocycle (orbitP6SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent6Table coverageP6HBasis
    orbitP6_hbasis_cocycle _

def orbitP6TargetCocycle (k : Fin 4) :=
  Order16Table.hCocycle parent6Table coverageP6HBasis (orbitP6TargetCoeff k)
theorem orbitP6TargetCocycle_consistent (k : Fin 4) :
    IsCentralCocycle (orbitP6TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent6Table coverageP6HBasis
    orbitP6_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
