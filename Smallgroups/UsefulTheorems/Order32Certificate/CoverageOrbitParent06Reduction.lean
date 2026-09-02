/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP6HCocycle (c : Fin 2 → F2) :=
  Order16Table.hCocycle parent6Table coverageP6HBasis c
theorem orbitP6HCocycle_consistent (c : Fin 2 → F2) :
    IsCentralCocycle (orbitP6HCocycle c) :=
  Order16Table.hCocycle_consistent parent6Table coverageP6HBasis
    orbitP6_hbasis_cocycle c

theorem orbitP6_cocycle_reduces_to_H
    (f : Order16Table.Q parent6Table → Order16Table.Q parent6Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 2 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP6HCocycle c) (orbitP6HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent6Table f
  have hvdecode : Order16Table.decodeTwo parent6Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent6Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent6Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP6_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent6Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent6Table d
  have hshift : f = addCoboundary (orbitP6HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent6Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent6Table
          (Order16Table.coboundaryVec parent6Table d +
            synthesizeTwo coverageP6HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent6Table
            (Order16Table.coboundaryVec parent6Table d) a b +
          Order16Table.decodeTwo parent6Table
            (synthesizeTwo coverageP6HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent6Table) F2 cochain a b +
          orbitP6HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP6HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP6HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP6HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP6_coeffMask_vecIndex : ∀ (c : Fin 2 → F2) (i : Fin 2),
    coeffMask 2 (vecIndex 2 c).val i = c i := by
  decide +kernel

theorem orbitP6_cocycle_orbit_complete
    (f : Order16Table.Q parent6Table → Order16Table.Q parent6Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 4, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP6SelectedCocycle o) (orbitP6SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP6_cocycle_reduces_to_H f hf
  let k : Fin 4 := vecIndex 2 c
  have hcoeff : orbitP6TargetCoeff k = c := by
    funext i
    exact orbitP6_coeffMask_vecIndex c i
  have hcocycle : orbitP6TargetCocycle k = orbitP6HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent6Table coverageP6HBasis) hcoeff
  refine ⟨orbitP6Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP6NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
