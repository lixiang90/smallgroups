/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP4HCocycle (c : Fin 3 → F2) :=
  Order16Table.hCocycle parent4Table coverageP4HBasis c
theorem orbitP4HCocycle_consistent (c : Fin 3 → F2) :
    IsCentralCocycle (orbitP4HCocycle c) :=
  Order16Table.hCocycle_consistent parent4Table coverageP4HBasis
    orbitP4_hbasis_cocycle c

theorem orbitP4_cocycle_reduces_to_H
    (f : Order16Table.Q parent4Table → Order16Table.Q parent4Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 3 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP4HCocycle c) (orbitP4HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent4Table f
  have hvdecode : Order16Table.decodeTwo parent4Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent4Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent4Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP4_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent4Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent4Table d
  have hshift : f = addCoboundary (orbitP4HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent4Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent4Table
          (Order16Table.coboundaryVec parent4Table d +
            synthesizeTwo coverageP4HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent4Table
            (Order16Table.coboundaryVec parent4Table d) a b +
          Order16Table.decodeTwo parent4Table
            (synthesizeTwo coverageP4HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent4Table) F2 cochain a b +
          orbitP4HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP4HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP4HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP4HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP4_coeffMask_vecIndex : ∀ (c : Fin 3 → F2) (i : Fin 3),
    coeffMask 3 (vecIndex 3 c).val i = c i := by
  decide +kernel

theorem orbitP4_cocycle_orbit_complete
    (f : Order16Table.Q parent4Table → Order16Table.Q parent4Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 6, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP4SelectedCocycle o) (orbitP4SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP4_cocycle_reduces_to_H f hf
  let k : Fin 8 := vecIndex 3 c
  have hcoeff : orbitP4TargetCoeff k = c := by
    funext i
    exact orbitP4_coeffMask_vecIndex c i
  have hcocycle : orbitP4TargetCocycle k = orbitP4HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent4Table coverageP4HBasis) hcoeff
  refine ⟨orbitP4Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP4NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
