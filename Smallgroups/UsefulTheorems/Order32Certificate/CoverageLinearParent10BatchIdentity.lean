/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent10Data
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent09BatchIdentity

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 10. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP10_packed_certificate :
    Order16Table.PackedCoverageCertificate parent10Table
      coverageP10TotalBasis coverageP10CoordinateRows coverageP10EquationTriples
      coverageP10CorrectionColumns coverageP10PackedCoordinateMasks
      coverageP10PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP10_reduction_identity_batched : coverageP10ReductionMap = LinearMap.id := by
  unfold coverageP10ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent10Table
    coverageP10TotalBasis coverageP10CoordinateRows coverageP10EquationTriples
    coverageP10CorrectionColumns coverageP10PackedCoordinateMasks
    coverageP10PackedEquationMasks coverageP10_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
