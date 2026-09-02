/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP7HCocycle (c : Fin 3 → F2) :=
  Order16Table.hCocycle parent7Table coverageP7HBasis c
theorem orbitP7HCocycle_consistent (c : Fin 3 → F2) :
    IsCentralCocycle (orbitP7HCocycle c) :=
  Order16Table.hCocycle_consistent parent7Table coverageP7HBasis
    orbitP7_hbasis_cocycle c

theorem orbitP7_cocycle_reduces_to_H
    (f : Order16Table.Q parent7Table → Order16Table.Q parent7Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 3 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP7HCocycle c) (orbitP7HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent7Table f
  have hvdecode : Order16Table.decodeTwo parent7Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent7Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent7Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP7_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent7Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent7Table d
  have hshift : f = addCoboundary (orbitP7HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent7Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent7Table
          (Order16Table.coboundaryVec parent7Table d +
            synthesizeTwo coverageP7HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent7Table
            (Order16Table.coboundaryVec parent7Table d) a b +
          Order16Table.decodeTwo parent7Table
            (synthesizeTwo coverageP7HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent7Table) F2 cochain a b +
          orbitP7HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP7HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP7HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP7HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP7_coeffMask_vecIndex : ∀ (c : Fin 3 → F2) (i : Fin 3),
    coeffMask 3 (vecIndex 3 c).val i = c i := by
  decide +kernel

theorem orbitP7_cocycle_orbit_complete
    (f : Order16Table.Q parent7Table → Order16Table.Q parent7Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 6, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP7SelectedCocycle o) (orbitP7SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP7_cocycle_reduces_to_H f hf
  let k : Fin 8 := vecIndex 3 c
  have hcoeff : orbitP7TargetCoeff k = c := by
    funext i
    exact orbitP7_coeffMask_vecIndex c i
  have hcocycle : orbitP7TargetCocycle k = orbitP7HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent7Table coverageP7HBasis) hcoeff
  refine ⟨orbitP7Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP7NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
