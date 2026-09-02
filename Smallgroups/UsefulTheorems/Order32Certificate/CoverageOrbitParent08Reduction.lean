/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP8HCocycle (c : Fin 2 → F2) :=
  Order16Table.hCocycle parent8Table coverageP8HBasis c
theorem orbitP8HCocycle_consistent (c : Fin 2 → F2) :
    IsCentralCocycle (orbitP8HCocycle c) :=
  Order16Table.hCocycle_consistent parent8Table coverageP8HBasis
    orbitP8_hbasis_cocycle c

theorem orbitP8_cocycle_reduces_to_H
    (f : Order16Table.Q parent8Table → Order16Table.Q parent8Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 2 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP8HCocycle c) (orbitP8HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent8Table f
  have hvdecode : Order16Table.decodeTwo parent8Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent8Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent8Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP8_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent8Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent8Table d
  have hshift : f = addCoboundary (orbitP8HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent8Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent8Table
          (Order16Table.coboundaryVec parent8Table d +
            synthesizeTwo coverageP8HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent8Table
            (Order16Table.coboundaryVec parent8Table d) a b +
          Order16Table.decodeTwo parent8Table
            (synthesizeTwo coverageP8HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent8Table) F2 cochain a b +
          orbitP8HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP8HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP8HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP8HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP8_coeffMask_vecIndex : ∀ (c : Fin 2 → F2) (i : Fin 2),
    coeffMask 2 (vecIndex 2 c).val i = c i := by
  decide +kernel

theorem orbitP8_cocycle_orbit_complete
    (f : Order16Table.Q parent8Table → Order16Table.Q parent8Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 4, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP8SelectedCocycle o) (orbitP8SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP8_cocycle_reduces_to_H f hf
  let k : Fin 4 := vecIndex 2 c
  have hcoeff : orbitP8TargetCoeff k = c := by
    funext i
    exact orbitP8_coeffMask_vecIndex c i
  have hcocycle : orbitP8TargetCocycle k = orbitP8HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent8Table coverageP8HBasis) hcoeff
  refine ⟨orbitP8Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP8NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
