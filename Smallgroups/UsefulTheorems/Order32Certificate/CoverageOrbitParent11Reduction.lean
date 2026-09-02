/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11PathIdentity
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Decomposition

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP11HCocycle (c : Fin 6 → F2) :=
  Order16Table.hCocycle parent11Table coverageP11HBasis c
theorem orbitP11HCocycle_consistent (c : Fin 6 → F2) :
    IsCentralCocycle (orbitP11HCocycle c) :=
  Order16Table.hCocycle_consistent parent11Table coverageP11HBasis
    orbitP11_hbasis_cocycle c

theorem orbitP11_cocycle_reduces_to_H
    (f : Order16Table.Q parent11Table → Order16Table.Q parent11Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ c : Fin 6 → F2, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP11HCocycle c) (orbitP11HCocycle_consistent c)) := by
  let v := Order16Table.encodeTwo parent11Table f
  have hvdecode : Order16Table.decodeTwo parent11Table v = f :=
    Order16Table.decodeTwo_encodeTwo parent11Table hf
  have hv : IsCentralCocycle (Order16Table.decodeTwo parent11Table v) := by
    rw [hvdecode]
    exact hf
  obtain ⟨d, c, hdecomp⟩ := orbitP11_decompose_cocycle v hv
  let cochain := Order16Table.decodeOne parent11Table d
  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent11Table d
  have hshift : f = addCoboundary (orbitP11HCocycle c) cochain := by
    funext a b
    calc
      f a b = Order16Table.decodeTwo parent11Table v a b := by rw [hvdecode]
      _ = Order16Table.decodeTwo parent11Table
          (Order16Table.coboundaryVec parent11Table d +
            synthesizeTwo coverageP11HBasis c) a b := by rw [hdecomp]
      _ = Order16Table.decodeTwo parent11Table
            (Order16Table.coboundaryVec parent11Table d) a b +
          Order16Table.decodeTwo parent11Table
            (synthesizeTwo coverageP11HBasis c) a b :=
            Order16Table.decodeTwo_add _ _ _ _ _
      _ = centralCoboundary (Order16Table.Q parent11Table) F2 cochain a b +
          orbitP11HCocycle c a b := by
            rw [Order16Table.decodeTwo_coboundaryVec]
            rfl
      _ = addCoboundary (orbitP11HCocycle c) cochain a b := by
            simp [addCoboundary, centralCoboundary]
            abel
  refine ⟨c, ⟨?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq hf
    ((orbitP11HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans
      (CocycleGroup.coboundaryEquiv (orbitP11HCocycle_consistent c) cochain hcochain)

set_option maxHeartbeats 8000000 in
-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.
theorem orbitP11_coeffMask_vecIndex : ∀ (c : Fin 6 → F2) (i : Fin 6),
    coeffMask 6 (vecIndex 6 c).val i = c i := by
  decide +kernel

theorem orbitP11_cocycle_orbit_complete
    (f : Order16Table.Q parent11Table → Order16Table.Q parent11Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 18, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP11SelectedCocycle o) (orbitP11SelectedCocycle_consistent o)) := by
  obtain ⟨c, ⟨e⟩⟩ := orbitP11_cocycle_reduces_to_H f hf
  let k : Fin 64 := vecIndex 6 c
  have hcoeff : orbitP11TargetCoeff k = c := by
    funext i
    exact orbitP11_coeffMask_vecIndex c i
  have hcocycle : orbitP11TargetCocycle k = orbitP11HCocycle c := by
    exact congrArg (Order16Table.hCocycle parent11Table coverageP11HBasis) hcoeff
  refine ⟨orbitP11Index k, ⟨e.trans ?_⟩⟩
  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans
    (orbitP11NormalizeEquiv k).symm

end Smallgroups.UsefulTheorems.Order32Certificate
