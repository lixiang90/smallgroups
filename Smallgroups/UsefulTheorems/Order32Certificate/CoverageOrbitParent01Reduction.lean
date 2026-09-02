/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP1HCocycle (c : Fin 1 → F2) :=
  Order16Table.hCocycle parent1Table coverageP1HBasis c
theorem orbitP1HCocycle_consistent (c : Fin 1 → F2) :
    IsCentralCocycle (orbitP1HCocycle c) :=
  Order16Table.hCocycle_consistent parent1Table coverageP1HBasis
    orbitP1_hbasis_cocycle c

theorem orbitP1_cocycle_reduces_to_H
    (f : Order16Table.Q parent1Table → Order16Table.Q parent1Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 1 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP1HCocycle c) (orbitP1HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent1Table f
  have hvdecode : Order16Table.decodeTwo parent1Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent1Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent1Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP1_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent1Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent1Table d
  have hshift : f = addCoboundary (orbitP1HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent1Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent1Table
          (Order16Table.coboundaryVec parent1Table d +
            synthesizeTwo coverageP1HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent1Table
            (Order16Table.coboundaryVec parent1Table d) a b +
          Order16Table.decodeTwo parent1Table
            (synthesizeTwo coverageP1HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent1Table) F2 cochain a b +
          orbitP1HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP1HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP1HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP1HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP1_coeffMask_vecIndex : ∀ (c : Fin 1 → F2) (i : Fin 1),
    coeffMask 1 (vecIndex 1 c).val i = c i := by
  decide +kernel

theorem orbitP1_cocycle_orbit_complete
    (f : Order16Table.Q parent1Table → Order16Table.Q parent1Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP1SelectedCocycle o) (orbitP1SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP1_cocycle_reduces_to_H f hf
  let k : Fin 2 := vecIndex 1 c
  have hcoeff : orbitP1TargetCoeff k = c := by
    funext i
    exact orbitP1_coeffMask_vecIndex c i
  have hcocycle : orbitP1TargetCocycle k = orbitP1HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent1Table coverageP1HBasis) hcoeff
  refine ⟨orbitP1Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP1NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
