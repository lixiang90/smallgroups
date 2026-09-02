/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent06Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Core

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,6)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP6RepresentativeMask : Fin 4 → ℕ :=
  ![0, 1, 2, 3]
def orbitP6Index : Fin 4 → Fin 4 :=
  ![0, 1, 2, 3]
def orbitP6AutPerm : Fin 4 → Fin 16 → Fin 16 :=
  ![![0, 5, 2, 10, 4, 1, 15, 12, 14, 9, 3, 13, 7, 11, 8, 6], ![0, 6, 2, 10, 4, 11, 1, 13, 14, 9, 3, 5, 15, 7, 8, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11]]
def orbitP6AutInvPerm : Fin 4 → Fin 16 → Fin 16 :=
  ![![0, 5, 2, 10, 4, 1, 15, 12, 14, 9, 3, 13, 7, 11, 8, 6], ![0, 6, 2, 10, 4, 11, 1, 13, 14, 9, 3, 5, 15, 7, 8, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11]]
def orbitP6ActionColumns : Fin 4 → Fin 2 → ℕ :=
  ![![1, 2], ![1, 2], ![1, 2], ![1, 2]]
def orbitP6CorrectionColumns : Fin 4 → Fin 2 → ℕ :=
  ![![2903, 6966], ![0, 0], ![0, 0], ![0, 0]]

def orbitP6RepresentativeCoeff (k : Fin 4) : Fin 2 → F2 :=
  coeffMask 2 (orbitP6RepresentativeMask (orbitP6Index k))
def orbitP6TargetCoeff (k : Fin 4) : Fin 2 → F2 :=
  coeffMask 2 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
