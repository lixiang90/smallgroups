/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Data

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 7. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP7AutCertificate (g : Fin 5) : Prop :=
  (∀ a : Fin 16, orbitP7AutInvPerm g (orbitP7AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP7AutPerm g (orbitP7AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP7AutPerm g (parent7Table.mul a b) =
    parent7Table.mul (orbitP7AutPerm g a) (orbitP7AutPerm g b))

theorem orbitP7_aut_certificate : ∀ g : Fin 5, orbitP7AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP7AutCertificate <;> decide +kernel

def orbitP7Aut (g : Fin 5) :
    Order16Table.Q parent7Table ≃* Order16Table.Q parent7Table where
  toFun x := ⟨orbitP7AutPerm g x.val⟩
  invFun x := ⟨orbitP7AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP7_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP7_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP7_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP7_action_linear (g : Fin 5) :
    (Order16Table.precomposeTwoLinear parent7Table (orbitP7Aut g)).comp
        ((Order16Table.decodeTwoLinear parent7Table).comp
          (synthesizeTwo coverageP7HBasis)) =
      (Order16Table.centralCoboundaryLinear parent7Table).comp
          (Order16Table.orbitCorrection parent7Table
            (orbitP7CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent7Table).comp
          ((synthesizeTwo coverageP7HBasis).comp
            (Order16Table.orbitAction (orbitP7ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 3)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP7SelectedCocycle (o : Fin 6) :=
  Order16Table.hCocycle parent7Table coverageP7HBasis
    (coeffMask 3 (orbitP7RepresentativeMask o))
theorem orbitP7SelectedCocycle_consistent (o : Fin 6) :
    IsCentralCocycle (orbitP7SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent7Table coverageP7HBasis
    orbitP7_hbasis_cocycle _

def orbitP7TargetCocycle (k : Fin 8) :=
  Order16Table.hCocycle parent7Table coverageP7HBasis (orbitP7TargetCoeff k)
theorem orbitP7TargetCocycle_consistent (k : Fin 8) :
    IsCentralCocycle (orbitP7TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent7Table coverageP7HBasis
    orbitP7_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
