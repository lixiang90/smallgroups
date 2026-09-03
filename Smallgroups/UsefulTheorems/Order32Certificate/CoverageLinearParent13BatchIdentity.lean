/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent13Data

set_option maxRecDepth 100000

/-! One batched kernel check of all 225 reduction columns for parent 13. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 100000000 in
-- The proposition contains only finite bit-vector computations.
theorem coverageP13_packed_certificate :
    Order16Table.PackedCoverageCertificate parent13Table
      coverageP13TotalBasis coverageP13CoordinateRows coverageP13EquationTriples
      coverageP13CorrectionColumns coverageP13PackedCoordinateMasks
      coverageP13PackedEquationMasks := by
  unfold Order16Table.PackedCoverageCertificate
  decide +kernel

theorem coverageP13_reduction_identity_batched : coverageP13ReductionMap = LinearMap.id := by
  unfold coverageP13ReductionMap
  exact Order16Table.reductionIdentityOfPackedCertificate parent13Table
    coverageP13TotalBasis coverageP13CoordinateRows coverageP13EquationTriples
    coverageP13CorrectionColumns coverageP13PackedCoordinateMasks
    coverageP13PackedEquationMasks coverageP13_packed_certificate

end Smallgroups.UsefulTheorems.Order32Certificate
