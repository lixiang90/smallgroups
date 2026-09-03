/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent02Data

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 2. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP2_packed_certificate :
    Order16Table.PackedCoverageCertificate parent2Table
      coverageP2TotalBasis coverageP2CoordinateRows coverageP2EquationTriples
      coverageP2CorrectionColumns coverageP2PackedCoordinateMasks
      coverageP2PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP2_reduction_identity_batched : coverageP2ReductionMap = LinearMap.id := by
  unfold coverageP2ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent2Table
    coverageP2TotalBasis coverageP2CoordinateRows coverageP2EquationTriples
    coverageP2CorrectionColumns coverageP2PackedCoordinateMasks
    coverageP2PackedEquationMasks coverageP2_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
