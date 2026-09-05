/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03Data

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 3. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP3AutCertificate (g : Fin 5) : Prop :=
  (∀ a : Fin 16, orbitP3AutInvPerm g (orbitP3AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP3AutPerm g (orbitP3AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP3AutPerm g (parent3Table.mul a b) =
    parent3Table.mul (orbitP3AutPerm g a) (orbitP3AutPerm g b))

theorem orbitP3_aut_certificate : ∀ g : Fin 5, orbitP3AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP3AutCertificate <;> decide +kernel

def orbitP3Aut (g : Fin 5) :
    Order16Table.Q parent3Table ≃* Order16Table.Q parent3Table where
  toFun x := ⟨orbitP3AutPerm g x.val⟩
  invFun x := ⟨orbitP3AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP3_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP3_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP3_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP3_action_linear (g : Fin 5) :
    (Order16Table.precomposeTwoLinear parent3Table (orbitP3Aut g)).comp
        ((Order16Table.decodeTwoLinear parent3Table).comp
          (synthesizeTwo coverageP3HBasis)) =
      (Order16Table.centralCoboundaryLinear parent3Table).comp
          (Order16Table.orbitCorrection parent3Table
            (orbitP3CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent3Table).comp
          ((synthesizeTwo coverageP3HBasis).comp
            (Order16Table.orbitAction (orbitP3ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 4)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP3SelectedCocycle (o : Fin 9) :=
  Order16Table.hCocycle parent3Table coverageP3HBasis
    (coeffMask 4 (orbitP3RepresentativeMask o))
theorem orbitP3SelectedCocycle_consistent (o : Fin 9) :
    IsCentralCocycle (orbitP3SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent3Table coverageP3HBasis
    orbitP3_hbasis_cocycle _

def orbitP3TargetCocycle (k : Fin 16) :=
  Order16Table.hCocycle parent3Table coverageP3HBasis (orbitP3TargetCoeff k)
theorem orbitP3TargetCocycle_consistent (k : Fin 16) :
    IsCentralCocycle (orbitP3TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent3Table coverageP3HBasis
    orbitP3_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
