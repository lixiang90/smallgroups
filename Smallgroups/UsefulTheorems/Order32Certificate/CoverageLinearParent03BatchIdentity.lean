/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent03Data

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 3. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP3_packed_certificate :
    Order16Table.PackedCoverageCertificate parent3Table
      coverageP3TotalBasis coverageP3CoordinateRows coverageP3EquationTriples
      coverageP3CorrectionColumns coverageP3PackedCoordinateMasks
      coverageP3PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP3_reduction_identity_batched : coverageP3ReductionMap = LinearMap.id := by
  unfold coverageP3ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent3Table
    coverageP3TotalBasis coverageP3CoordinateRows coverageP3EquationTriples
    coverageP3CorrectionColumns coverageP3PackedCoordinateMasks
    coverageP3PackedEquationMasks coverageP3_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
