/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageParent14PackedData

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 14. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem parent14_packed_certificate :
    Order16Table.PackedCoverageCertificate parent14Table
      parent14TotalBasis parent14CoordinateRows parent14EquationTriples
      parent14CorrectionColumns parent14PackedCoordinateMasks
      parent14PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem parent14_reduction_identity_batched : parent14ReductionMap = LinearMap.id := by
  unfold parent14ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent14Table
    parent14TotalBasis parent14CoordinateRows parent14EquationTriples
    parent14CorrectionColumns parent14PackedCoordinateMasks
    parent14PackedEquationMasks parent14_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
