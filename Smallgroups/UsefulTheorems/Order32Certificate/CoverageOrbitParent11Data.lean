/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent11Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,11)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP11RepresentativeMask : Fin 18 → ℕ :=
  ![0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 21, 23, 32, 36, 37, 40, 45, 49]
def orbitP11Index : Fin 64 → Fin 18 :=
  ![0, 1, 2, 3, 4, 5, 5, 4, 1, 6, 3, 7, 8, 9, 9, 8, 4, 8, 5, 9, 3, 10, 1, 11, 5, 9, 4, 8, 10, 3, 11, 1, 12, 12, 12, 12, 13, 14, 13, 14, 15, 15, 15, 15, 14, 16, 14, 16, 14, 17, 14, 17, 12, 15, 12, 15, 17, 14, 17, 14, 12, 15, 12, 15]
def orbitP11AutPerm : Fin 6 → Fin 16 → Fin 16 :=
  ![![0, 2, 1, 3, 4, 12, 8, 9, 6, 7, 10, 15, 5, 14, 13, 11], ![0, 1, 8, 3, 4, 11, 6, 7, 2, 14, 10, 5, 15, 13, 9, 12], ![0, 6, 2, 3, 4, 11, 1, 13, 8, 9, 10, 5, 15, 7, 14, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11], ![0, 1, 2, 10, 4, 5, 13, 7, 14, 9, 3, 15, 12, 6, 8, 11]]
def orbitP11AutInvPerm : Fin 6 → Fin 16 → Fin 16 :=
  ![![0, 2, 1, 3, 4, 12, 8, 9, 6, 7, 10, 15, 5, 14, 13, 11], ![0, 1, 8, 3, 4, 11, 6, 7, 2, 14, 10, 5, 15, 13, 9, 12], ![0, 6, 2, 3, 4, 11, 1, 13, 8, 9, 10, 5, 15, 7, 14, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11], ![0, 1, 2, 10, 4, 5, 13, 7, 14, 9, 3, 15, 12, 6, 8, 11]]
def orbitP11ActionColumns : Fin 6 → Fin 6 → ℕ :=
  ![![8, 2, 16, 1, 4, 52], ![31, 2, 26, 22, 16, 62], ![22, 2, 4, 31, 7, 32], ![1, 2, 4, 8, 16, 32], ![1, 2, 4, 8, 16, 32], ![1, 2, 4, 8, 16, 34]]
def orbitP11CorrectionColumns : Fin 6 → Fin 6 → ℕ :=
  ![![0, 2580, 0, 0, 0, 15], ![4009, 1278, 581, 1278, 581, 553], ![1278, 1469, 774, 4009, 2322, 683], ![0, 0, 0, 0, 0, 2714], ![0, 0, 0, 0, 0, 2875], ![0, 0, 0, 0, 0, 2059]]

def orbitP11RepresentativeCoeff (k : Fin 64) : Fin 6 → F2 :=
  coeffMask 6 (orbitP11RepresentativeMask (orbitP11Index k))
def orbitP11TargetCoeff (k : Fin 64) : Fin 6 → F2 :=
  coeffMask 6 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
