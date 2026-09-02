/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP3HCocycle (c : Fin 4 → F2) :=
  Order16Table.hCocycle parent3Table coverageP3HBasis c
theorem orbitP3HCocycle_consistent (c : Fin 4 → F2) :
    IsCentralCocycle (orbitP3HCocycle c) :=
  Order16Table.hCocycle_consistent parent3Table coverageP3HBasis
    orbitP3_hbasis_cocycle c

theorem orbitP3_cocycle_reduces_to_H
    (f : Order16Table.Q parent3Table → Order16Table.Q parent3Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 4 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP3HCocycle c) (orbitP3HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent3Table f
  have hvdecode : Order16Table.decodeTwo parent3Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent3Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent3Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP3_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent3Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent3Table d
  have hshift : f = addCoboundary (orbitP3HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent3Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent3Table
          (Order16Table.coboundaryVec parent3Table d +
            synthesizeTwo coverageP3HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent3Table
            (Order16Table.coboundaryVec parent3Table d) a b +
          Order16Table.decodeTwo parent3Table
            (synthesizeTwo coverageP3HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent3Table) F2 cochain a b +
          orbitP3HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP3HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP3HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP3HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP3_coeffMask_vecIndex : ∀ (c : Fin 4 → F2) (i : Fin 4),
    coeffMask 4 (vecIndex 4 c).val i = c i := by
  decide +kernel

theorem orbitP3_cocycle_orbit_complete
    (f : Order16Table.Q parent3Table → Order16Table.Q parent3Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 9, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP3SelectedCocycle o) (orbitP3SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP3_cocycle_reduces_to_H f hf
  let k : Fin 16 := vecIndex 4 c
  have hcoeff : orbitP3TargetCoeff k = c := by
    funext i
    exact orbitP3_coeffMask_vecIndex c i
  have hcocycle : orbitP3TargetCocycle k = orbitP3HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent3Table coverageP3HBasis) hcoeff
  refine ⟨orbitP3Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP3NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
