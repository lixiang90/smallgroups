/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent09Data

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 9. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP9_packed_certificate :
    Order16Table.PackedCoverageCertificate parent9Table
      coverageP9TotalBasis coverageP9CoordinateRows coverageP9EquationTriples
      coverageP9CorrectionColumns coverageP9PackedCoordinateMasks
      coverageP9PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP9_reduction_identity_batched : coverageP9ReductionMap = LinearMap.id := by
  unfold coverageP9ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent9Table
    coverageP9TotalBasis coverageP9CoordinateRows coverageP9EquationTriples
    coverageP9CorrectionColumns coverageP9PackedCoordinateMasks
    coverageP9PackedEquationMasks coverageP9_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
