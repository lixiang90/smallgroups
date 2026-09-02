/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent05Data
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent04BatchIdentity

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 5. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP5_packed_certificate :
    Order16Table.PackedCoverageCertificate parent5Table
      coverageP5TotalBasis coverageP5CoordinateRows coverageP5EquationTriples
      coverageP5CorrectionColumns coverageP5PackedCoordinateMasks
      coverageP5PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP5_reduction_identity_batched : coverageP5ReductionMap = LinearMap.id := by
  unfold coverageP5ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent5Table
    coverageP5TotalBasis coverageP5CoordinateRows coverageP5EquationTriples
    coverageP5CorrectionColumns coverageP5PackedCoordinateMasks
    coverageP5PackedEquationMasks coverageP5_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
