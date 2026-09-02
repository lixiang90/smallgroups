/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP14HCocycle (c : Fin 10 → F2) :=
  Order16Table.hCocycle parent14Table parent14HBasis c
theorem orbitP14HCocycle_consistent (c : Fin 10 → F2) :
    IsCentralCocycle (orbitP14HCocycle c) :=
  Order16Table.hCocycle_consistent parent14Table parent14HBasis
    orbitP14_hbasis_cocycle c

theorem orbitP14_cocycle_reduces_to_H
    (f : Order16Table.Q parent14Table → Order16Table.Q parent14Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 10 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP14HCocycle c) (orbitP14HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent14Table f
  have hvdecode : Order16Table.decodeTwo parent14Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent14Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent14Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP14_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent14Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent14Table d
  have hshift : f = addCoboundary (orbitP14HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent14Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent14Table
          (Order16Table.coboundaryVec parent14Table d +
            synthesizeTwo parent14HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent14Table
            (Order16Table.coboundaryVec parent14Table d) a b +
          Order16Table.decodeTwo parent14Table
            (synthesizeTwo parent14HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent14Table) F2 cochain a b +
          orbitP14HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP14HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP14HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP14HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP14_coeffMask_vecIndex : ∀ (c : Fin 10 → F2) (i : Fin 10),
    coeffMask 10 (vecIndex 10 c).val i = c i := by
  decide +kernel

theorem orbitP14_cocycle_orbit_complete
    (f : Order16Table.Q parent14Table → Order16Table.Q parent14Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 7, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP14SelectedCocycle o) (orbitP14SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP14_cocycle_reduces_to_H f hf
  let k : Fin 1024 := vecIndex 10 c
  have hcoeff : orbitP14TargetCoeff k = c := by
    funext i
    exact orbitP14_coeffMask_vecIndex c i
  have hcocycle : orbitP14TargetCocycle k = orbitP14HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent14Table parent14HBasis) hcoeff
  refine ⟨orbitP14Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP14NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
