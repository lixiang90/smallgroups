/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Data

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 4. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP4_hbasis_cocycle (i : Fin 3) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent4Table (twoMask (coverageP4HBasis i))) := by
  fin_cases i <;> decide +kernel

def orbitP4AutCertificate (g : Fin 5) : Prop :=
  (∀ a : Fin 16, orbitP4AutInvPerm g (orbitP4AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP4AutPerm g (orbitP4AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP4AutPerm g (parent4Table.mul a b) =
    parent4Table.mul (orbitP4AutPerm g a) (orbitP4AutPerm g b))

theorem orbitP4_aut_certificate : ∀ g : Fin 5, orbitP4AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP4AutCertificate <;> decide +kernel

def orbitP4Aut (g : Fin 5) :
    Order16Table.Q parent4Table ≃* Order16Table.Q parent4Table where
  toFun x := ⟨orbitP4AutPerm g x.val⟩
  invFun x := ⟨orbitP4AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP4_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP4_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP4_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP4_action_linear (g : Fin 5) :
    (Order16Table.precomposeTwoLinear parent4Table (orbitP4Aut g)).comp
        ((Order16Table.decodeTwoLinear parent4Table).comp
          (synthesizeTwo coverageP4HBasis)) =
      (Order16Table.centralCoboundaryLinear parent4Table).comp
          (Order16Table.orbitCorrection parent4Table
            (orbitP4CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent4Table).comp
          ((synthesizeTwo coverageP4HBasis).comp
            (Order16Table.orbitAction (orbitP4ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 3)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP4SelectedCocycle (o : Fin 6) :=
  Order16Table.hCocycle parent4Table coverageP4HBasis
    (coeffMask 3 (orbitP4RepresentativeMask o))
theorem orbitP4SelectedCocycle_consistent (o : Fin 6) :
    IsCentralCocycle (orbitP4SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent4Table coverageP4HBasis
    orbitP4_hbasis_cocycle _

def orbitP4TargetCocycle (k : Fin 8) :=
  Order16Table.hCocycle parent4Table coverageP4HBasis (orbitP4TargetCoeff k)
theorem orbitP4TargetCocycle_consistent (k : Fin 8) :
    IsCentralCocycle (orbitP4TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent4Table coverageP4HBasis
    orbitP4_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
