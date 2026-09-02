/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP10HCocycle (c : Fin 6 → F2) :=
  Order16Table.hCocycle parent10Table coverageP10HBasis c
theorem orbitP10HCocycle_consistent (c : Fin 6 → F2) :
    IsCentralCocycle (orbitP10HCocycle c) :=
  Order16Table.hCocycle_consistent parent10Table coverageP10HBasis
    orbitP10_hbasis_cocycle c

theorem orbitP10_cocycle_reduces_to_H
    (f : Order16Table.Q parent10Table → Order16Table.Q parent10Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 6 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP10HCocycle c) (orbitP10HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent10Table f
  have hvdecode : Order16Table.decodeTwo parent10Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent10Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent10Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP10_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent10Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent10Table d
  have hshift : f = addCoboundary (orbitP10HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent10Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent10Table
          (Order16Table.coboundaryVec parent10Table d +
            synthesizeTwo coverageP10HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent10Table
            (Order16Table.coboundaryVec parent10Table d) a b +
          Order16Table.decodeTwo parent10Table
            (synthesizeTwo coverageP10HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent10Table) F2 cochain a b +
          orbitP10HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP10HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP10HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP10HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP10_coeffMask_vecIndex : ∀ (c : Fin 6 → F2) (i : Fin 6),
    coeffMask 6 (vecIndex 6 c).val i = c i := by
  decide +kernel

theorem orbitP10_cocycle_orbit_complete
    (f : Order16Table.Q parent10Table → Order16Table.Q parent10Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 10, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP10SelectedCocycle o) (orbitP10SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP10_cocycle_reduces_to_H f hf
  let k : Fin 64 := vecIndex 6 c
  have hcoeff : orbitP10TargetCoeff k = c := by
    funext i
    exact orbitP10_coeffMask_vecIndex c i
  have hcocycle : orbitP10TargetCocycle k = orbitP10HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent10Table coverageP10HBasis) hcoeff
  refine ⟨orbitP10Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP10NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
