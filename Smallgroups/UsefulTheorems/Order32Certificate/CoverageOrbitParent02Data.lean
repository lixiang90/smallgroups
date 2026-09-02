/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent02Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01Core

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,2)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP2RepresentativeMask : Fin 4 → ℕ :=
  ![0, 1, 2, 3]
def orbitP2Index : Fin 8 → Fin 4 :=
  ![0, 1, 2, 3, 1, 1, 3, 3]
def orbitP2AutPerm : Fin 4 → Fin 16 → Fin 16 :=
  ![![0, 2, 1, 4, 3, 5, 9, 8, 7, 6, 10, 12, 11, 14, 13, 15], ![0, 2, 1, 4, 3, 5, 9, 8, 7, 6, 10, 12, 11, 14, 13, 15], ![0, 5, 2, 10, 4, 7, 15, 12, 14, 9, 3, 6, 1, 11, 8, 13], ![0, 6, 2, 3, 4, 11, 1, 13, 8, 9, 10, 5, 15, 7, 14, 12]]
def orbitP2AutInvPerm : Fin 4 → Fin 16 → Fin 16 :=
  ![![0, 2, 1, 4, 3, 5, 9, 8, 7, 6, 10, 12, 11, 14, 13, 15], ![0, 2, 1, 4, 3, 5, 9, 8, 7, 6, 10, 12, 11, 14, 13, 15], ![0, 12, 2, 10, 4, 1, 11, 5, 14, 9, 3, 13, 7, 15, 8, 6], ![0, 6, 2, 3, 4, 11, 1, 13, 8, 9, 10, 5, 15, 7, 14, 12]]
def orbitP2ActionColumns : Fin 4 → Fin 3 → ℕ :=
  ![![1, 2, 5], ![1, 2, 5], ![4, 2, 1], ![1, 2, 4]]
def orbitP2CorrectionColumns : Fin 4 → Fin 3 → ℕ :=
  ![![3084, 7565, 1028], ![3084, 7565, 1028], ![5855, 3621, 219], ![5974, 4193, 33]]

def orbitP2RepresentativeCoeff (k : Fin 8) : Fin 3 → F2 :=
  coeffMask 3 (orbitP2RepresentativeMask (orbitP2Index k))
def orbitP2TargetCoeff (k : Fin 8) : Fin 3 → F2 :=
  coeffMask 3 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
