/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02Data
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01Core

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP2_hbasis_cocycle (i : Fin 3) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent2Table (twoMask (coverageP2HBasis i))) := by
  fin_cases i <;> decide +kernel

def orbitP2AutCertificate (g : Fin 4) : Prop :=
  (∀ a : Fin 16, orbitP2AutInvPerm g (orbitP2AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP2AutPerm g (orbitP2AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP2AutPerm g (parent2Table.mul a b) =
    parent2Table.mul (orbitP2AutPerm g a) (orbitP2AutPerm g b))

theorem orbitP2_aut_certificate : ∀ g : Fin 4, orbitP2AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP2AutCertificate <;> decide +kernel

def orbitP2Aut (g : Fin 4) :
    Order16Table.Q parent2Table ≃* Order16Table.Q parent2Table where
  toFun x := ⟨orbitP2AutPerm g x.val⟩
  invFun x := ⟨orbitP2AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP2_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP2_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP2_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP2_action_linear (g : Fin 4) :
    (Order16Table.precomposeTwoLinear parent2Table (orbitP2Aut g)).comp
        ((Order16Table.decodeTwoLinear parent2Table).comp
          (synthesizeTwo coverageP2HBasis)) =
      (Order16Table.centralCoboundaryLinear parent2Table).comp
          (Order16Table.orbitCorrection parent2Table
            (orbitP2CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent2Table).comp
          ((synthesizeTwo coverageP2HBasis).comp
            (Order16Table.orbitAction (orbitP2ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 3)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP2SelectedCocycle (o : Fin 4) :=
  Order16Table.hCocycle parent2Table coverageP2HBasis
    (coeffMask 3 (orbitP2RepresentativeMask o))
theorem orbitP2SelectedCocycle_consistent (o : Fin 4) :
    IsCentralCocycle (orbitP2SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent2Table coverageP2HBasis
    orbitP2_hbasis_cocycle _

def orbitP2TargetCocycle (k : Fin 8) :=
  Order16Table.hCocycle parent2Table coverageP2HBasis (orbitP2TargetCoeff k)
theorem orbitP2TargetCocycle_consistent (k : Fin 8) :
    IsCentralCocycle (orbitP2TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent2Table coverageP2HBasis
    orbitP2_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
