/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP13HCocycle (c : Fin 5 → F2) :=
  Order16Table.hCocycle parent13Table coverageP13HBasis c
theorem orbitP13HCocycle_consistent (c : Fin 5 → F2) :
    IsCentralCocycle (orbitP13HCocycle c) :=
  Order16Table.hCocycle_consistent parent13Table coverageP13HBasis
    orbitP13_hbasis_cocycle c

theorem orbitP13_cocycle_reduces_to_H
    (f : Order16Table.Q parent13Table → Order16Table.Q parent13Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 5 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP13HCocycle c) (orbitP13HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent13Table f
  have hvdecode : Order16Table.decodeTwo parent13Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent13Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent13Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP13_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent13Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent13Table d
  have hshift : f = addCoboundary (orbitP13HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent13Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent13Table
          (Order16Table.coboundaryVec parent13Table d +
            synthesizeTwo coverageP13HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent13Table
            (Order16Table.coboundaryVec parent13Table d) a b +
          Order16Table.decodeTwo parent13Table
            (synthesizeTwo coverageP13HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent13Table) F2 cochain a b +
          orbitP13HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP13HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP13HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP13HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP13_coeffMask_vecIndex : ∀ (c : Fin 5 → F2) (i : Fin 5),
    coeffMask 5 (vecIndex 5 c).val i = c i := by
  decide +kernel

theorem orbitP13_cocycle_orbit_complete
    (f : Order16Table.Q parent13Table → Order16Table.Q parent13Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 10, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP13SelectedCocycle o) (orbitP13SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP13_cocycle_reduces_to_H f hf
  let k : Fin 32 := vecIndex 5 c
  have hcoeff : orbitP13TargetCoeff k = c := by
    funext i
    exact orbitP13_coeffMask_vecIndex c i
  have hcocycle : orbitP13TargetCocycle k = orbitP13HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent13Table coverageP13HBasis) hcoeff
  refine ⟨orbitP13Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP13NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
