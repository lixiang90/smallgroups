/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Data
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Core

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 8. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP8_hbasis_cocycle (i : Fin 2) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent8Table (twoMask (coverageP8HBasis i))) := by
  fin_cases i <;> decide +kernel

def orbitP8AutCertificate (g : Fin 4) : Prop :=
  (∀ a : Fin 16, orbitP8AutInvPerm g (orbitP8AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP8AutPerm g (orbitP8AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP8AutPerm g (parent8Table.mul a b) =
    parent8Table.mul (orbitP8AutPerm g a) (orbitP8AutPerm g b))

theorem orbitP8_aut_certificate : ∀ g : Fin 4, orbitP8AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP8AutCertificate <;> decide +kernel

def orbitP8Aut (g : Fin 4) :
    Order16Table.Q parent8Table ≃* Order16Table.Q parent8Table where
  toFun x := ⟨orbitP8AutPerm g x.val⟩
  invFun x := ⟨orbitP8AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP8_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP8_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP8_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP8_action_linear (g : Fin 4) :
    (Order16Table.precomposeTwoLinear parent8Table (orbitP8Aut g)).comp
        ((Order16Table.decodeTwoLinear parent8Table).comp
          (synthesizeTwo coverageP8HBasis)) =
      (Order16Table.centralCoboundaryLinear parent8Table).comp
          (Order16Table.orbitCorrection parent8Table
            (orbitP8CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent8Table).comp
          ((synthesizeTwo coverageP8HBasis).comp
            (Order16Table.orbitAction (orbitP8ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 2)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP8SelectedCocycle (o : Fin 4) :=
  Order16Table.hCocycle parent8Table coverageP8HBasis
    (coeffMask 2 (orbitP8RepresentativeMask o))
theorem orbitP8SelectedCocycle_consistent (o : Fin 4) :
    IsCentralCocycle (orbitP8SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent8Table coverageP8HBasis
    orbitP8_hbasis_cocycle _

def orbitP8TargetCocycle (k : Fin 4) :=
  Order16Table.hCocycle parent8Table coverageP8HBasis (orbitP8TargetCoeff k)
theorem orbitP8TargetCocycle_consistent (k : Fin 4) :
    IsCentralCocycle (orbitP8TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent8Table coverageP8HBasis
    orbitP8_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
