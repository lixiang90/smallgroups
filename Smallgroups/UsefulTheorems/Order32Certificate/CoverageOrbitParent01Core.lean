/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01Data
import Smallgroups.UsefulTheorems.Order32Certificate.Parent14OrbitAlignmentPart07

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP1_hbasis_cocycle (i : Fin 1) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent1Table (twoMask (coverageP1HBasis i))) := by
  fin_cases i
  decide +kernel

def orbitP1AutCertificate (g : Fin 2) : Prop :=
  (∀ a : Fin 16, orbitP1AutInvPerm g (orbitP1AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP1AutPerm g (orbitP1AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP1AutPerm g (parent1Table.mul a b) =
    parent1Table.mul (orbitP1AutPerm g a) (orbitP1AutPerm g b))

theorem orbitP1_aut_certificate : ∀ g : Fin 2, orbitP1AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP1AutCertificate <;> decide +kernel

def orbitP1Aut (g : Fin 2) :
    Order16Table.Q parent1Table ≃* Order16Table.Q parent1Table where
  toFun x := ⟨orbitP1AutPerm g x.val⟩
  invFun x := ⟨orbitP1AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP1_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP1_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP1_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP1_action_linear (g : Fin 2) :
    (Order16Table.precomposeTwoLinear parent1Table (orbitP1Aut g)).comp
        ((Order16Table.decodeTwoLinear parent1Table).comp
          (synthesizeTwo coverageP1HBasis)) =
      (Order16Table.centralCoboundaryLinear parent1Table).comp
          (Order16Table.orbitCorrection parent1Table
            (orbitP1CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent1Table).comp
          ((synthesizeTwo coverageP1HBasis).comp
            (Order16Table.orbitAction (orbitP1ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 1)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP1SelectedCocycle (o : Fin 2) :=
  Order16Table.hCocycle parent1Table coverageP1HBasis
    (coeffMask 1 (orbitP1RepresentativeMask o))
theorem orbitP1SelectedCocycle_consistent (o : Fin 2) :
    IsCentralCocycle (orbitP1SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent1Table coverageP1HBasis
    orbitP1_hbasis_cocycle _

def orbitP1TargetCocycle (k : Fin 2) :=
  Order16Table.hCocycle parent1Table coverageP1HBasis (orbitP1TargetCoeff k)
theorem orbitP1TargetCocycle_consistent (k : Fin 2) :
    IsCentralCocycle (orbitP1TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent1Table coverageP1HBasis
    orbitP1_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
