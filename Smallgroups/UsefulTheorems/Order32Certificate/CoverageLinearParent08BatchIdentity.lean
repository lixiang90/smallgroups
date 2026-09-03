/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent08Data

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 8. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP8_packed_certificate :
    Order16Table.PackedCoverageCertificate parent8Table
      coverageP8TotalBasis coverageP8CoordinateRows coverageP8EquationTriples
      coverageP8CorrectionColumns coverageP8PackedCoordinateMasks
      coverageP8PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP8_reduction_identity_batched : coverageP8ReductionMap = LinearMap.id := by
  unfold coverageP8ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent8Table
    coverageP8TotalBasis coverageP8CoordinateRows coverageP8EquationTriples
    coverageP8CorrectionColumns coverageP8PackedCoordinateMasks
    coverageP8PackedEquationMasks coverageP8_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
