/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent13Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,13)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP13RepresentativeMask : Fin 10 → ℕ :=
  ![0, 1, 2, 3, 4, 8, 10, 13, 24, 26]
def orbitP13Index : Fin 32 → Fin 10 :=
  ![0, 1, 2, 3, 4, 2, 3, 2, 5, 3, 6, 1, 4, 7, 3, 7, 4, 7, 1, 6, 5, 3, 7, 3, 8, 6, 9, 7, 5, 9, 7, 9]
def orbitP13AutPerm : Fin 5 → Fin 16 → Fin 16 :=
  ![![0, 11, 2, 3, 4, 6, 12, 15, 8, 9, 10, 7, 13, 5, 14, 1], ![0, 11, 1, 3, 4, 14, 12, 15, 6, 7, 10, 2, 8, 5, 13, 9], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11], ![0, 1, 2, 10, 4, 5, 13, 7, 14, 9, 3, 15, 12, 6, 8, 11]]
def orbitP13AutInvPerm : Fin 5 → Fin 16 → Fin 16 :=
  ![![0, 15, 2, 3, 4, 13, 5, 11, 8, 9, 10, 1, 6, 12, 14, 7], ![0, 2, 11, 3, 4, 13, 8, 9, 12, 15, 10, 1, 6, 14, 5, 7], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11], ![0, 1, 2, 10, 4, 5, 13, 7, 14, 9, 3, 15, 12, 6, 8, 11]]
def orbitP13ActionColumns : Fin 5 → Fin 5 → ℕ :=
  ![![1, 7, 4, 20, 12], ![18, 7, 16, 20, 12], ![1, 2, 4, 8, 16], ![1, 2, 4, 8, 16], ![1, 2, 4, 8, 16]]
def orbitP13CorrectionColumns : Fin 5 → Fin 5 → ℕ :=
  ![![0, 0, 0, 854, 1895], ![383, 2322, 1409, 2628, 3813], ![0, 0, 0, 2903, 774], ![0, 0, 0, 2903, 2064], ![0, 0, 0, 323, 2322]]

def orbitP13RepresentativeCoeff (k : Fin 32) : Fin 5 → F2 :=
  coeffMask 5 (orbitP13RepresentativeMask (orbitP13Index k))
def orbitP13TargetCoeff (k : Fin 32) : Fin 5 → F2 :=
  coeffMask 5 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
