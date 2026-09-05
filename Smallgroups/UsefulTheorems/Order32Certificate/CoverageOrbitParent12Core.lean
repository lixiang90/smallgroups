/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Data

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 12. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP12AutCertificate (g : Fin 7) : Prop :=
  (∀ a : Fin 16, orbitP12AutInvPerm g (orbitP12AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP12AutPerm g (orbitP12AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP12AutPerm g (parent12Table.mul a b) =
    parent12Table.mul (orbitP12AutPerm g a) (orbitP12AutPerm g b))

theorem orbitP12_aut_certificate : ∀ g : Fin 7, orbitP12AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP12AutCertificate <;> decide +kernel

def orbitP12Aut (g : Fin 7) :
    Order16Table.Q parent12Table ≃* Order16Table.Q parent12Table where
  toFun x := ⟨orbitP12AutPerm g x.val⟩
  invFun x := ⟨orbitP12AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP12_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP12_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP12_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP12_action_linear (g : Fin 7) :
    (Order16Table.precomposeTwoLinear parent12Table (orbitP12Aut g)).comp
        ((Order16Table.decodeTwoLinear parent12Table).comp
          (synthesizeTwo coverageP12HBasis)) =
      (Order16Table.centralCoboundaryLinear parent12Table).comp
          (Order16Table.orbitCorrection parent12Table
            (orbitP12CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent12Table).comp
          ((synthesizeTwo coverageP12HBasis).comp
            (Order16Table.orbitAction (orbitP12ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 5)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP12SelectedCocycle (o : Fin 6) :=
  Order16Table.hCocycle parent12Table coverageP12HBasis
    (coeffMask 5 (orbitP12RepresentativeMask o))
theorem orbitP12SelectedCocycle_consistent (o : Fin 6) :
    IsCentralCocycle (orbitP12SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent12Table coverageP12HBasis
    orbitP12_hbasis_cocycle _

def orbitP12TargetCocycle (k : Fin 32) :=
  Order16Table.hCocycle parent12Table coverageP12HBasis (orbitP12TargetCoeff k)
theorem orbitP12TargetCocycle_consistent (k : Fin 32) :
    IsCentralCocycle (orbitP12TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent12Table coverageP12HBasis
    orbitP12_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
