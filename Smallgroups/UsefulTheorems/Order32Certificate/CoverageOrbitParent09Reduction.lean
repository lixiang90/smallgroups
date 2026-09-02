/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP9HCocycle (c : Fin 2 → F2) :=
  Order16Table.hCocycle parent9Table coverageP9HBasis c
theorem orbitP9HCocycle_consistent (c : Fin 2 → F2) :
    IsCentralCocycle (orbitP9HCocycle c) :=
  Order16Table.hCocycle_consistent parent9Table coverageP9HBasis
    orbitP9_hbasis_cocycle c

theorem orbitP9_cocycle_reduces_to_H
    (f : Order16Table.Q parent9Table → Order16Table.Q parent9Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 2 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP9HCocycle c) (orbitP9HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent9Table f
  have hvdecode : Order16Table.decodeTwo parent9Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent9Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent9Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP9_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent9Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent9Table d
  have hshift : f = addCoboundary (orbitP9HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent9Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent9Table
          (Order16Table.coboundaryVec parent9Table d +
            synthesizeTwo coverageP9HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent9Table
            (Order16Table.coboundaryVec parent9Table d) a b +
          Order16Table.decodeTwo parent9Table
            (synthesizeTwo coverageP9HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent9Table) F2 cochain a b +
          orbitP9HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP9HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP9HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP9HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP9_coeffMask_vecIndex : ∀ (c : Fin 2 → F2) (i : Fin 2),
    coeffMask 2 (vecIndex 2 c).val i = c i := by
  decide +kernel

theorem orbitP9_cocycle_orbit_complete
    (f : Order16Table.Q parent9Table → Order16Table.Q parent9Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 3, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP9SelectedCocycle o) (orbitP9SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP9_cocycle_reduces_to_H f hf
  let k : Fin 4 := vecIndex 2 c
  have hcoeff : orbitP9TargetCoeff k = c := by
    funext i
    exact orbitP9_coeffMask_vecIndex c i
  have hcocycle : orbitP9TargetCocycle k = orbitP9HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent9Table coverageP9HBasis) hcoeff
  refine ⟨orbitP9Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP9NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
