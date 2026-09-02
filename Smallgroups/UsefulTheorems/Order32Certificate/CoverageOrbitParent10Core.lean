/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Data
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Core

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 10. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP10_hbasis_cocycle (i : Fin 6) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent10Table (twoMask (coverageP10HBasis i))) := by
  fin_cases i <;> decide +kernel

def orbitP10AutCertificate (g : Fin 7) : Prop :=
  (∀ a : Fin 16, orbitP10AutInvPerm g (orbitP10AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP10AutPerm g (orbitP10AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP10AutPerm g (parent10Table.mul a b) =
    parent10Table.mul (orbitP10AutPerm g a) (orbitP10AutPerm g b))

theorem orbitP10_aut_certificate : ∀ g : Fin 7, orbitP10AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP10AutCertificate <;> decide +kernel

def orbitP10Aut (g : Fin 7) :
    Order16Table.Q parent10Table ≃* Order16Table.Q parent10Table where
  toFun x := ⟨orbitP10AutPerm g x.val⟩
  invFun x := ⟨orbitP10AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP10_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP10_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP10_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP10_action_linear (g : Fin 7) :
    (Order16Table.precomposeTwoLinear parent10Table (orbitP10Aut g)).comp
        ((Order16Table.decodeTwoLinear parent10Table).comp
          (synthesizeTwo coverageP10HBasis)) =
      (Order16Table.centralCoboundaryLinear parent10Table).comp
          (Order16Table.orbitCorrection parent10Table
            (orbitP10CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent10Table).comp
          ((synthesizeTwo coverageP10HBasis).comp
            (Order16Table.orbitAction (orbitP10ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 6)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP10SelectedCocycle (o : Fin 10) :=
  Order16Table.hCocycle parent10Table coverageP10HBasis
    (coeffMask 6 (orbitP10RepresentativeMask o))
theorem orbitP10SelectedCocycle_consistent (o : Fin 10) :
    IsCentralCocycle (orbitP10SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent10Table coverageP10HBasis
    orbitP10_hbasis_cocycle _

def orbitP10TargetCocycle (k : Fin 64) :=
  Order16Table.hCocycle parent10Table coverageP10HBasis (orbitP10TargetCoeff k)
theorem orbitP10TargetCocycle_consistent (k : Fin 64) :
    IsCentralCocycle (orbitP10TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent10Table coverageP10HBasis
    orbitP10_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
