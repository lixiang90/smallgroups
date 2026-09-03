/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14ForestData

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Parent-14 orbit-forest edge certificate, chunk 12. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- Kernel reduction checks 64 independently generated orbit-forest edges.
theorem orbitP14_forest_chunk_11 : ∀ j : Fin 64,
    Order16Table.OrbitForestEdge orbitP14ActionColumns
      orbitP14RepresentativeCoeff orbitP14TargetCoeff orbitP14ForestParent
      orbitP14ForestGenerator orbitP14ForestRank
      (orbitP14ForestChunkIndex 11 j) := by
  unfold Order16Table.OrbitForestEdge
  decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
