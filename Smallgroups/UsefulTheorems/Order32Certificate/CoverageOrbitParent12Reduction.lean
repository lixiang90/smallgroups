/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP12HCocycle (c : Fin 5 → F2) :=
  Order16Table.hCocycle parent12Table coverageP12HBasis c
theorem orbitP12HCocycle_consistent (c : Fin 5 → F2) :
    IsCentralCocycle (orbitP12HCocycle c) :=
  Order16Table.hCocycle_consistent parent12Table coverageP12HBasis
    orbitP12_hbasis_cocycle c

theorem orbitP12_cocycle_reduces_to_H
    (f : Order16Table.Q parent12Table → Order16Table.Q parent12Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 5 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP12HCocycle c) (orbitP12HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent12Table f
  have hvdecode : Order16Table.decodeTwo parent12Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent12Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent12Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP12_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent12Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent12Table d
  have hshift : f = addCoboundary (orbitP12HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent12Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent12Table
          (Order16Table.coboundaryVec parent12Table d +
            synthesizeTwo coverageP12HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent12Table
            (Order16Table.coboundaryVec parent12Table d) a b +
          Order16Table.decodeTwo parent12Table
            (synthesizeTwo coverageP12HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent12Table) F2 cochain a b +
          orbitP12HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP12HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP12HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP12HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP12_coeffMask_vecIndex : ∀ (c : Fin 5 → F2) (i : Fin 5),
    coeffMask 5 (vecIndex 5 c).val i = c i := by
  decide +kernel

theorem orbitP12_cocycle_orbit_complete
    (f : Order16Table.Q parent12Table → Order16Table.Q parent12Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 6, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP12SelectedCocycle o) (orbitP12SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP12_cocycle_reduces_to_H f hf
  let k : Fin 32 := vecIndex 5 c
  have hcoeff : orbitP12TargetCoeff k = c := by
    funext i
    exact orbitP12_coeffMask_vecIndex c i
  have hcocycle : orbitP12TargetCocycle k = orbitP12HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent12Table coverageP12HBasis) hcoeff
  refine ⟨orbitP12Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP12NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
