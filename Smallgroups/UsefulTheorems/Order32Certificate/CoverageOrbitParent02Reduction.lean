/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP2HCocycle (c : Fin 3 → F2) :=
  Order16Table.hCocycle parent2Table coverageP2HBasis c
theorem orbitP2HCocycle_consistent (c : Fin 3 → F2) :
    IsCentralCocycle (orbitP2HCocycle c) :=
  Order16Table.hCocycle_consistent parent2Table coverageP2HBasis
    orbitP2_hbasis_cocycle c

theorem orbitP2_cocycle_reduces_to_H
    (f : Order16Table.Q parent2Table → Order16Table.Q parent2Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 3 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP2HCocycle c) (orbitP2HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent2Table f
  have hvdecode : Order16Table.decodeTwo parent2Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent2Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent2Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP2_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent2Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent2Table d
  have hshift : f = addCoboundary (orbitP2HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent2Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent2Table
          (Order16Table.coboundaryVec parent2Table d +
            synthesizeTwo coverageP2HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent2Table
            (Order16Table.coboundaryVec parent2Table d) a b +
          Order16Table.decodeTwo parent2Table
            (synthesizeTwo coverageP2HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent2Table) F2 cochain a b +
          orbitP2HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP2HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP2HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP2HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP2_coeffMask_vecIndex : ∀ (c : Fin 3 → F2) (i : Fin 3),
    coeffMask 3 (vecIndex 3 c).val i = c i := by
  decide +kernel

theorem orbitP2_cocycle_orbit_complete
    (f : Order16Table.Q parent2Table → Order16Table.Q parent2Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 4, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP2SelectedCocycle o) (orbitP2SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP2_cocycle_reduces_to_H f hf
  let k : Fin 8 := vecIndex 3 c
  have hcoeff : orbitP2TargetCoeff k = c := by
    funext i
    exact orbitP2_coeffMask_vecIndex c i
  have hcocycle : orbitP2TargetCocycle k = orbitP2HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent2Table coverageP2HBasis) hcoeff
  refine ⟨orbitP2Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP2NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
