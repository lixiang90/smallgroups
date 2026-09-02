/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Data
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked generator action for parent 14. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_hbasis_cocycle (i : Fin 10) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent14Table (twoMask (parent14HBasis i))) := by
  fin_cases i <;> decide +kernel

def orbitP14AutCertificate (g : Fin 4) : Prop :=
  (∀ a : Fin 16, orbitP14AutInvPerm g (orbitP14AutPerm g a) = a) ∧
  (∀ a : Fin 16, orbitP14AutPerm g (orbitP14AutInvPerm g a) = a) ∧
  (∀ a b : Fin 16, orbitP14AutPerm g (parent14Table.mul a b) =
    parent14Table.mul (orbitP14AutPerm g a) (orbitP14AutPerm g b))

theorem orbitP14_aut_certificate : ∀ g : Fin 4, orbitP14AutCertificate g := by
  intro g
  fin_cases g <;> unfold orbitP14AutCertificate <;> decide +kernel

def orbitP14Aut (g : Fin 4) :
    Order16Table.Q parent14Table ≃* Order16Table.Q parent14Table where
  toFun x := ⟨orbitP14AutPerm g x.val⟩
  invFun x := ⟨orbitP14AutInvPerm g x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP14_aut_certificate g).1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact (orbitP14_aut_certificate g).2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact (orbitP14_aut_certificate g).2.2 x.val y.val

set_option maxHeartbeats 8000000 in
-- Each column check establishes the action and coboundary correction on one H² basis vector.
theorem orbitP14_action_linear (g : Fin 4) :
    (Order16Table.precomposeTwoLinear parent14Table (orbitP14Aut g)).comp
        ((Order16Table.decodeTwoLinear parent14Table).comp
          (synthesizeTwo parent14HBasis)) =
      (Order16Table.centralCoboundaryLinear parent14Table).comp
          (Order16Table.orbitCorrection parent14Table
            (orbitP14CorrectionColumns g)) +
        (Order16Table.decodeTwoLinear parent14Table).comp
          ((synthesizeTwo parent14HBasis).comp
            (Order16Table.orbitAction (orbitP14ActionColumns g))) := by
  apply (Pi.basisFun F2 (Fin 10)).ext
  simp_rw [Pi.basisFun_apply]
  intro i
  ext a b
  fin_cases g <;> fin_cases i <;> decide +kernel +revert

def orbitP14SelectedCocycle (o : Fin 7) :=
  Order16Table.hCocycle parent14Table parent14HBasis
    (coeffMask 10 (orbitP14RepresentativeMask o))
theorem orbitP14SelectedCocycle_consistent (o : Fin 7) :
    IsCentralCocycle (orbitP14SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent14Table parent14HBasis
    orbitP14_hbasis_cocycle _

def orbitP14TargetCocycle (k : Fin 1024) :=
  Order16Table.hCocycle parent14Table parent14HBasis (orbitP14TargetCoeff k)
theorem orbitP14TargetCocycle_consistent (k : Fin 1024) :
    IsCentralCocycle (orbitP14TargetCocycle k) :=
  Order16Table.hCocycle_consistent parent14Table parent14HBasis
    orbitP14_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
