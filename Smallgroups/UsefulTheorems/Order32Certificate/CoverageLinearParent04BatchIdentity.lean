/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent04Data
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent03BatchIdentity

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 4. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP4_packed_certificate :
    Order16Table.PackedCoverageCertificate parent4Table
      coverageP4TotalBasis coverageP4CoordinateRows coverageP4EquationTriples
      coverageP4CorrectionColumns coverageP4PackedCoordinateMasks
      coverageP4PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP4_reduction_identity_batched : coverageP4ReductionMap = LinearMap.id := by
  unfold coverageP4ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent4Table
    coverageP4TotalBasis coverageP4CoordinateRows coverageP4EquationTriples
    coverageP4CorrectionColumns coverageP4PackedCoordinateMasks
    coverageP4PackedEquationMasks coverageP4_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
