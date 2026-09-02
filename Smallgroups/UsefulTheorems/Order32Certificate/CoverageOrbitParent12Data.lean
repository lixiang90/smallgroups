/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent12Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Core

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,12)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP12RepresentativeMask : Fin 6 → ℕ :=
  ![0, 1, 2, 3, 9, 13]
def orbitP12Index : Fin 32 → Fin 6 :=
  ![0, 1, 2, 3, 2, 3, 3, 2, 1, 4, 3, 2, 3, 5, 5, 3, 2, 3, 3, 5, 3, 5, 1, 4, 3, 5, 2, 3, 5, 3, 4, 1]
def orbitP12AutPerm : Fin 7 → Fin 16 → Fin 16 :=
  ![![0, 1, 11, 3, 4, 14, 6, 7, 5, 15, 10, 9, 8, 13, 12, 2], ![0, 11, 6, 3, 4, 2, 5, 15, 1, 13, 10, 8, 9, 12, 7, 14], ![0, 1, 8, 3, 4, 11, 6, 7, 2, 14, 10, 5, 15, 13, 9, 12], ![0, 6, 2, 3, 4, 11, 1, 13, 8, 9, 10, 5, 15, 7, 14, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11], ![0, 1, 2, 10, 4, 5, 13, 7, 14, 9, 3, 15, 12, 6, 8, 11]]
def orbitP12AutInvPerm : Fin 7 → Fin 16 → Fin 16 :=
  ![![0, 1, 15, 3, 4, 8, 6, 7, 12, 11, 10, 2, 14, 13, 5, 9], ![0, 8, 5, 3, 4, 6, 2, 14, 11, 12, 10, 1, 13, 9, 15, 7], ![0, 1, 8, 3, 4, 11, 6, 7, 2, 14, 10, 5, 15, 13, 9, 12], ![0, 6, 2, 3, 4, 11, 1, 13, 8, 9, 10, 5, 15, 7, 14, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11], ![0, 1, 2, 10, 4, 5, 13, 7, 14, 9, 3, 15, 12, 6, 8, 11]]
def orbitP12ActionColumns : Fin 7 → Fin 5 → ℕ :=
  ![![22, 26, 11, 8, 16], ![1, 7, 2, 22, 26], ![22, 11, 26, 31, 16], ![31, 11, 4, 22, 7], ![1, 2, 4, 8, 16], ![1, 2, 4, 8, 16], ![1, 2, 4, 8, 16]]
def orbitP12CorrectionColumns : Fin 7 → Fin 5 → ℕ :=
  ![![3818, 581, 1469, 0, 0], ![0, 0, 0, 3818, 581], ![3818, 1469, 581, 1469, 581], ![1469, 1278, 774, 3818, 2322], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]

def orbitP12RepresentativeCoeff (k : Fin 32) : Fin 5 → F2 :=
  coeffMask 5 (orbitP12RepresentativeMask (orbitP12Index k))
def orbitP12TargetCoeff (k : Fin 32) : Fin 5 → F2 :=
  coeffMask 5 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
