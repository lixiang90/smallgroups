/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent06Data
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent05BatchIdentity

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 6. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP6_packed_certificate :
    Order16Table.PackedCoverageCertificate parent6Table
      coverageP6TotalBasis coverageP6CoordinateRows coverageP6EquationTriples
      coverageP6CorrectionColumns coverageP6PackedCoordinateMasks
      coverageP6PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP6_reduction_identity_batched : coverageP6ReductionMap = LinearMap.id := by
  unfold coverageP6ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent6Table
    coverageP6TotalBasis coverageP6CoordinateRows coverageP6EquationTriples
    coverageP6CorrectionColumns coverageP6PackedCoordinateMasks
    coverageP6PackedEquationMasks coverageP6_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
