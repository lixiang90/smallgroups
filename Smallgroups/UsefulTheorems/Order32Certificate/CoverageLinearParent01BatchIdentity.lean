/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent01Data

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 1. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP1_packed_certificate :
    Order16Table.PackedCoverageCertificate parent1Table
      coverageP1TotalBasis coverageP1CoordinateRows coverageP1EquationTriples
      coverageP1CorrectionColumns coverageP1PackedCoordinateMasks
      coverageP1PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP1_reduction_identity_batched : coverageP1ReductionMap = LinearMap.id := by
  unfold coverageP1ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent1Table
    coverageP1TotalBasis coverageP1CoordinateRows coverageP1EquationTriples
    coverageP1CorrectionColumns coverageP1PackedCoordinateMasks
    coverageP1PackedEquationMasks coverageP1_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
