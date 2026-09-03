/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Data

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 9. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP9_hbasis_cocycle (i : Fin 2) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent9Table (twoMask (coverageP9HBasis i))) := by
  fin_cases i <;> decide +kernel

def orbitP9AutCertificate (g : Fin 5) : Prop :=
  (∀ a : Fin 16, orbitP9AutInvPerm g (orbitP9AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP9AutPerm g (orbitP9AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP9AutPerm g (parent9Table.mul a b) =
    parent9Table.mul (orbitP9AutPerm g a) (orbitP9AutPerm g b))

theorem orbitP9_aut_certificate : ∀ g : Fin 5, orbitP9AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP9AutCertificate <;> decide +kernel

def orbitP9Aut (g : Fin 5) :
    Order16Table.Q parent9Table ≃* Order16Table.Q parent9Table where
  toFun x := ⟨orbitP9AutPerm g x.val⟩
  invFun x := ⟨orbitP9AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP9_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP9_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP9_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP9_action_linear (g : Fin 5) :
    (Order16Table.precomposeTwoLinear parent9Table (orbitP9Aut g)).comp
        ((Order16Table.decodeTwoLinear parent9Table).comp
          (synthesizeTwo coverageP9HBasis)) =
      (Order16Table.centralCoboundaryLinear parent9Table).comp
          (Order16Table.orbitCorrection parent9Table
            (orbitP9CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent9Table).comp
          ((synthesizeTwo coverageP9HBasis).comp
            (Order16Table.orbitAction (orbitP9ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 2)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP9SelectedCocycle (o : Fin 3) :=
  Order16Table.hCocycle parent9Table coverageP9HBasis
    (coeffMask 2 (orbitP9RepresentativeMask o))
theorem orbitP9SelectedCocycle_consistent (o : Fin 3) :
    IsCentralCocycle (orbitP9SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent9Table coverageP9HBasis
    orbitP9_hbasis_cocycle _

def orbitP9TargetCocycle (k : Fin 4) :=
  Order16Table.hCocycle parent9Table coverageP9HBasis (orbitP9TargetCoeff k)
theorem orbitP9TargetCocycle_consistent (k : Fin 4) :
    IsCentralCocycle (orbitP9TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent9Table coverageP9HBasis
    orbitP9_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
