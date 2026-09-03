/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent10Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,10)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP10RepresentativeMask : Fin 10 → ℕ :=
  ![0, 1, 2, 4, 5, 11, 12, 32, 34, 36]
def orbitP10Index : Fin 64 → Fin 10 :=
  ![0, 1, 2, 2, 3, 4, 2, 2, 1, 1, 2, 5, 6, 6, 5, 2, 2, 2, 4, 6, 2, 2, 6, 4, 2, 5, 3, 6, 5, 2, 3, 6, 7, 7, 8, 8, 9, 9, 8, 8, 7, 7, 8, 8, 9, 9, 8, 8, 8, 8, 9, 9, 8, 8, 9, 9, 8, 8, 9, 9, 8, 8, 9, 9]
def orbitP10AutPerm : Fin 7 → Fin 16 → Fin 16 :=
  ![![0, 1, 3, 2, 4, 6, 5, 7, 8, 10, 9, 11, 13, 12, 14, 15], ![0, 1, 3, 2, 4, 6, 5, 7, 8, 10, 9, 11, 13, 12, 14, 15], ![0, 1, 8, 3, 4, 11, 6, 7, 2, 14, 10, 5, 15, 13, 9, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11], ![0, 5, 2, 3, 4, 1, 11, 12, 8, 9, 10, 6, 7, 15, 14, 13]]
def orbitP10AutInvPerm : Fin 7 → Fin 16 → Fin 16 :=
  ![![0, 1, 3, 2, 4, 6, 5, 7, 8, 10, 9, 11, 13, 12, 14, 15], ![0, 1, 3, 2, 4, 6, 5, 7, 8, 10, 9, 11, 13, 12, 14, 15], ![0, 1, 8, 3, 4, 11, 6, 7, 2, 14, 10, 5, 15, 13, 9, 12], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11], ![0, 5, 2, 3, 4, 1, 11, 12, 8, 9, 10, 6, 7, 15, 14, 13]]
def orbitP10ActionColumns : Fin 7 → Fin 6 → ℕ :=
  ![![1, 3, 4, 9, 20, 33], ![1, 3, 4, 9, 20, 33], ![8, 21, 26, 1, 16, 41], ![1, 2, 4, 8, 16, 32], ![1, 2, 4, 8, 16, 32], ![1, 2, 4, 8, 16, 41], ![1, 16, 4, 8, 2, 32]]
def orbitP10CorrectionColumns : Fin 7 → Fin 6 → ℕ :=
  ![![0, 0, 0, 2580, 0, 2580], ![0, 0, 0, 2580, 0, 2580], ![1469, 3818, 581, 3818, 581, 2680], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 2714], ![0, 0, 0, 0, 0, 303], ![3818, 581, 774, 0, 2580, 1056]]

def orbitP10RepresentativeCoeff (k : Fin 64) : Fin 6 → F2 :=
  coeffMask 6 (orbitP10RepresentativeMask (orbitP10Index k))
def orbitP10TargetCoeff (k : Fin 64) : Fin 6 → F2 :=
  coeffMask 6 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
