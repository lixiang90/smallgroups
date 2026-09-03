/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Data

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 13. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP13_hbasis_cocycle (i : Fin 5) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent13Table (twoMask (coverageP13HBasis i))) := by
  fin_cases i <;> decide +kernel

def orbitP13AutCertificate (g : Fin 5) : Prop :=
  (∀ a : Fin 16, orbitP13AutInvPerm g (orbitP13AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP13AutPerm g (orbitP13AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP13AutPerm g (parent13Table.mul a b) =
    parent13Table.mul (orbitP13AutPerm g a) (orbitP13AutPerm g b))

theorem orbitP13_aut_certificate : ∀ g : Fin 5, orbitP13AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP13AutCertificate <;> decide +kernel

def orbitP13Aut (g : Fin 5) :
    Order16Table.Q parent13Table ≃* Order16Table.Q parent13Table where
  toFun x := ⟨orbitP13AutPerm g x.val⟩
  invFun x := ⟨orbitP13AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP13_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP13_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP13_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP13_action_linear (g : Fin 5) :
    (Order16Table.precomposeTwoLinear parent13Table (orbitP13Aut g)).comp
        ((Order16Table.decodeTwoLinear parent13Table).comp
          (synthesizeTwo coverageP13HBasis)) =
      (Order16Table.centralCoboundaryLinear parent13Table).comp
          (Order16Table.orbitCorrection parent13Table
            (orbitP13CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent13Table).comp
          ((synthesizeTwo coverageP13HBasis).comp
            (Order16Table.orbitAction (orbitP13ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 5)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP13SelectedCocycle (o : Fin 10) :=
  Order16Table.hCocycle parent13Table coverageP13HBasis
    (coeffMask 5 (orbitP13RepresentativeMask o))
theorem orbitP13SelectedCocycle_consistent (o : Fin 10) :
    IsCentralCocycle (orbitP13SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent13Table coverageP13HBasis
    orbitP13_hbasis_cocycle _

def orbitP13TargetCocycle (k : Fin 32) :=
  Order16Table.hCocycle parent13Table coverageP13HBasis (orbitP13TargetCoeff k)
theorem orbitP13TargetCocycle_consistent (k : Fin 32) :
    IsCentralCocycle (orbitP13TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent13Table coverageP13HBasis
    orbitP13_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
