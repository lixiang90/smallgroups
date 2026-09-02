/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent12Data
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent11BatchIdentity

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 12. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP12_packed_certificate :
    Order16Table.PackedCoverageCertificate parent12Table
      coverageP12TotalBasis coverageP12CoordinateRows coverageP12EquationTriples
      coverageP12CorrectionColumns coverageP12PackedCoordinateMasks
      coverageP12PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP12_reduction_identity_batched : coverageP12ReductionMap = LinearMap.id := by
  unfold coverageP12ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent12Table
    coverageP12TotalBasis coverageP12CoordinateRows coverageP12EquationTriples
    coverageP12CorrectionColumns coverageP12PackedCoordinateMasks
    coverageP12PackedEquationMasks coverageP12_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
