/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Data
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Core

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 5. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP5_hbasis_cocycle (i : Fin 3) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent5Table (twoMask (coverageP5HBasis i))) := by
  fin_cases i <;> decide +kernel

def orbitP5AutCertificate (g : Fin 5) : Prop :=
  (∀ a : Fin 16, orbitP5AutInvPerm g (orbitP5AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP5AutPerm g (orbitP5AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP5AutPerm g (parent5Table.mul a b) =
    parent5Table.mul (orbitP5AutPerm g a) (orbitP5AutPerm g b))

theorem orbitP5_aut_certificate : ∀ g : Fin 5, orbitP5AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP5AutCertificate <;> decide +kernel

def orbitP5Aut (g : Fin 5) :
    Order16Table.Q parent5Table ≃* Order16Table.Q parent5Table where
  toFun x := ⟨orbitP5AutPerm g x.val⟩
  invFun x := ⟨orbitP5AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP5_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP5_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP5_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP5_action_linear (g : Fin 5) :
    (Order16Table.precomposeTwoLinear parent5Table (orbitP5Aut g)).comp
        ((Order16Table.decodeTwoLinear parent5Table).comp
          (synthesizeTwo coverageP5HBasis)) =
      (Order16Table.centralCoboundaryLinear parent5Table).comp
          (Order16Table.orbitCorrection parent5Table
            (orbitP5CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent5Table).comp
          ((synthesizeTwo coverageP5HBasis).comp
            (Order16Table.orbitAction (orbitP5ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 3)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP5SelectedCocycle (o : Fin 6) :=
  Order16Table.hCocycle parent5Table coverageP5HBasis
    (coeffMask 3 (orbitP5RepresentativeMask o))
theorem orbitP5SelectedCocycle_consistent (o : Fin 6) :
    IsCentralCocycle (orbitP5SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent5Table coverageP5HBasis
    orbitP5_hbasis_cocycle _

def orbitP5TargetCocycle (k : Fin 8) :=
  Order16Table.hCocycle parent5Table coverageP5HBasis (orbitP5TargetCoeff k)
theorem orbitP5TargetCocycle_consistent (k : Fin 8) :
    IsCentralCocycle (orbitP5TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent5Table coverageP5HBasis
    orbitP5_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
