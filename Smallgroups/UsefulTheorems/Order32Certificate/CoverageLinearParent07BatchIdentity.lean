/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent07Data

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 7. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP7_packed_certificate :
    Order16Table.PackedCoverageCertificate parent7Table
      coverageP7TotalBasis coverageP7CoordinateRows coverageP7EquationTriples
      coverageP7CorrectionColumns coverageP7PackedCoordinateMasks
      coverageP7PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP7_reduction_identity_batched : coverageP7ReductionMap = LinearMap.id := by
  unfold coverageP7ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent7Table
    coverageP7TotalBasis coverageP7CoordinateRows coverageP7EquationTriples
    coverageP7CorrectionColumns coverageP7PackedCoordinateMasks
    coverageP7PackedEquationMasks coverageP7_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
