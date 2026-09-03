/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Data

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 11. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP11_hbasis_cocycle (i : Fin 6) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent11Table (twoMask (coverageP11HBasis i))) := by
  fin_cases i <;> decide +kernel

def orbitP11AutCertificate (g : Fin 6) : Prop :=
  (∀ a : Fin 16, orbitP11AutInvPerm g (orbitP11AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP11AutPerm g (orbitP11AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP11AutPerm g (parent11Table.mul a b) =
    parent11Table.mul (orbitP11AutPerm g a) (orbitP11AutPerm g b))

theorem orbitP11_aut_certificate : ∀ g : Fin 6, orbitP11AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP11AutCertificate <;> decide +kernel

def orbitP11Aut (g : Fin 6) :
    Order16Table.Q parent11Table ≃* Order16Table.Q parent11Table where
  toFun x := ⟨orbitP11AutPerm g x.val⟩
  invFun x := ⟨orbitP11AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP11_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP11_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP11_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP11_action_linear (g : Fin 6) :
    (Order16Table.precomposeTwoLinear parent11Table (orbitP11Aut g)).comp
        ((Order16Table.decodeTwoLinear parent11Table).comp
          (synthesizeTwo coverageP11HBasis)) =
      (Order16Table.centralCoboundaryLinear parent11Table).comp
          (Order16Table.orbitCorrection parent11Table
            (orbitP11CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent11Table).comp
          ((synthesizeTwo coverageP11HBasis).comp
            (Order16Table.orbitAction (orbitP11ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 6)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP11SelectedCocycle (o : Fin 18) :=
  Order16Table.hCocycle parent11Table coverageP11HBasis
    (coeffMask 6 (orbitP11RepresentativeMask o))
theorem orbitP11SelectedCocycle_consistent (o : Fin 18) :
    IsCentralCocycle (orbitP11SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent11Table coverageP11HBasis
    orbitP11_hbasis_cocycle _

def orbitP11TargetCocycle (k : Fin 64) :=
  Order16Table.hCocycle parent11Table coverageP11HBasis (orbitP11TargetCoeff k)
theorem orbitP11TargetCocycle_consistent (k : Fin 64) :
    IsCentralCocycle (orbitP11TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent11Table coverageP11HBasis
    orbitP11_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
