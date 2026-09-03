/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart01
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart02
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart03
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart04
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart05
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart06
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart07
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart08
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart09
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart10
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart11
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart12
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart13
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart14
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart15
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestPart16

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! One local edge check per H² vector certifies the parent-14 orbit forest. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_forest_chunks (c : Fin 16) : ∀ j : Fin 64,
    Order16Table.OrbitForestEdge orbitP14ActionColumns
      orbitP14RepresentativeCoeff orbitP14TargetCoeff orbitP14ForestParent
      orbitP14ForestGenerator orbitP14ForestRank
      (orbitP14ForestChunkIndex c j) := by
  fin_cases c
  · exact orbitP14_forest_chunk_00
  · exact orbitP14_forest_chunk_01
  · exact orbitP14_forest_chunk_02
  · exact orbitP14_forest_chunk_03
  · exact orbitP14_forest_chunk_04
  · exact orbitP14_forest_chunk_05
  · exact orbitP14_forest_chunk_06
  · exact orbitP14_forest_chunk_07
  · exact orbitP14_forest_chunk_08
  · exact orbitP14_forest_chunk_09
  · exact orbitP14_forest_chunk_10
  · exact orbitP14_forest_chunk_11
  · exact orbitP14_forest_chunk_12
  · exact orbitP14_forest_chunk_13
  · exact orbitP14_forest_chunk_14
  · exact orbitP14_forest_chunk_15

theorem orbitP14_forest_certificate :
    Order16Table.OrbitForestCertificate orbitP14ActionColumns
      orbitP14RepresentativeCoeff orbitP14TargetCoeff orbitP14ForestParent
      orbitP14ForestGenerator orbitP14ForestRank := by
  unfold Order16Table.OrbitForestCertificate
  intro k
  let c : Fin 16 := ⟨k.val / 64, by omega⟩
  let j : Fin 64 := ⟨k.val % 64, by omega⟩
  have hedge := orbitP14_forest_chunks c j
  have hindex : orbitP14ForestChunkIndex c j = k := by
    apply Fin.ext
    simp only [orbitP14ForestChunkIndex, c, j]
    omega
  rw [hindex] at hedge
  exact hedge

theorem orbitP14_forest_endpoint (k : Fin 1024) :
    Order16Table.applyOrbitPath orbitP14ActionColumns
        (Order16Table.orbitForestPath orbitP14ForestParent
          orbitP14ForestGenerator orbitP14ForestRank k)
        (orbitP14RepresentativeCoeff k) = orbitP14TargetCoeff k :=
  Order16Table.applyOrbitForestPath_eq orbitP14ActionColumns
    orbitP14RepresentativeCoeff orbitP14TargetCoeff orbitP14ForestParent
    orbitP14ForestGenerator orbitP14ForestRank orbitP14_forest_certificate k

noncomputable def orbitP14NormalizeEquiv (k : Fin 1024) :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index k))
        (orbitP14SelectedCocycle_consistent (orbitP14Index k)) ≃*
      CocycleGroup (orbitP14TargetCocycle k) (orbitP14TargetCocycle_consistent k) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear
    (Order16Table.orbitForestPath orbitP14ForestParent
      orbitP14ForestGenerator orbitP14ForestRank k) (orbitP14RepresentativeCoeff k)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      (orbitP14_forest_endpoint k)))

end Smallgroups.UsefulTheorems.Order32Certificate
