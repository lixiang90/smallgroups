/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent03Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,3)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP3RepresentativeMask : Fin 9 → ℕ :=
  ![0, 1, 2, 3, 6, 7, 9, 10, 15]
def orbitP3Index : Fin 16 → Fin 9 :=
  ![0, 1, 2, 3, 2, 3, 4, 5, 1, 6, 7, 2, 7, 2, 5, 8]
def orbitP3AutPerm : Fin 5 → Fin 16 → Fin 16 :=
  ![![0, 5, 2, 3, 10, 1, 11, 15, 8, 14, 4, 6, 13, 12, 9, 7], ![0, 6, 2, 3, 4, 11, 1, 13, 8, 9, 10, 5, 15, 7, 14, 12], ![0, 1, 8, 3, 4, 11, 6, 7, 2, 14, 10, 5, 15, 13, 9, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11]]
def orbitP3AutInvPerm : Fin 5 → Fin 16 → Fin 16 :=
  ![![0, 5, 2, 3, 10, 1, 11, 15, 8, 14, 4, 6, 13, 12, 9, 7], ![0, 6, 2, 3, 4, 11, 1, 13, 8, 9, 10, 5, 15, 7, 14, 12], ![0, 1, 8, 3, 4, 11, 6, 7, 2, 14, 10, 5, 15, 13, 9, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11]]
def orbitP3ActionColumns : Fin 5 → Fin 4 → ℕ :=
  ![![8, 11, 13, 1], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 4, 2, 8]]
def orbitP3CorrectionColumns : Fin 5 → Fin 4 → ℕ :=
  ![![5110, 6542, 285, 285], ![396, 1847, 5974, 5974], ![7649, 5814, 1751, 1751], ![396, 2779, 6842, 2129], ![7649, 5974, 1847, 6515]]

def orbitP3RepresentativeCoeff (k : Fin 16) : Fin 4 → F2 :=
  coeffMask 4 (orbitP3RepresentativeMask (orbitP3Index k))
def orbitP3TargetCoeff (k : Fin 16) : Fin 4 → F2 :=
  coeffMask 4 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
