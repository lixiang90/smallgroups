/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP5HCocycle (c : Fin 3 → F2) :=
  Order16Table.hCocycle parent5Table coverageP5HBasis c
theorem orbitP5HCocycle_consistent (c : Fin 3 → F2) :
    IsCentralCocycle (orbitP5HCocycle c) :=
  Order16Table.hCocycle_consistent parent5Table coverageP5HBasis
    orbitP5_hbasis_cocycle c

theorem orbitP5_cocycle_reduces_to_H
    (f : Order16Table.Q parent5Table → Order16Table.Q parent5Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 3 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP5HCocycle c) (orbitP5HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent5Table f
  have hvdecode : Order16Table.decodeTwo parent5Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent5Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent5Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP5_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent5Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent5Table d
  have hshift : f = addCoboundary (orbitP5HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent5Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent5Table
          (Order16Table.coboundaryVec parent5Table d +
            synthesizeTwo coverageP5HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent5Table
            (Order16Table.coboundaryVec parent5Table d) a b +
          Order16Table.decodeTwo parent5Table
            (synthesizeTwo coverageP5HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent5Table) F2 cochain a b +
          orbitP5HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP5HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP5HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP5HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP5_coeffMask_vecIndex : ∀ (c : Fin 3 → F2) (i : Fin 3),
    coeffMask 3 (vecIndex 3 c).val i = c i := by
  decide +kernel

theorem orbitP5_cocycle_orbit_complete
    (f : Order16Table.Q parent5Table → Order16Table.Q parent5Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 6, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP5SelectedCocycle o) (orbitP5SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP5_cocycle_reduces_to_H f hf
  let k : Fin 8 := vecIndex 3 c
  have hcoeff : orbitP5TargetCoeff k = c := by
    funext i
    exact orbitP5_coeffMask_vecIndex c i
  have hcocycle : orbitP5TargetCocycle k = orbitP5HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent5Table coverageP5HBasis) hcoeff
  refine ⟨orbitP5Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP5NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
