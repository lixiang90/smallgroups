/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent05Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,5)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP5RepresentativeMask : Fin 6 → ℕ :=
  ![0, 1, 2, 3, 4, 6]
def orbitP5Index : Fin 8 → Fin 6 :=
  ![0, 1, 2, 3, 4, 4, 5, 5]
def orbitP5AutPerm : Fin 5 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 13, 2, 10, 4, 15, 7, 6, 14, 9, 3, 12, 11, 1, 8, 5], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 7, 9, 3, 4, 5, 13, 1, 14, 2, 10, 11, 12, 6, 8, 15], ![0, 12, 2, 3, 4, 7, 15, 5, 8, 9, 10, 13, 1, 11, 14, 6]]
def orbitP5AutInvPerm : Fin 5 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![0, 13, 2, 10, 4, 15, 7, 6, 14, 9, 3, 12, 11, 1, 8, 5], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 7, 9, 3, 4, 5, 13, 1, 14, 2, 10, 11, 12, 6, 8, 15], ![0, 12, 2, 3, 4, 7, 15, 5, 8, 9, 10, 13, 1, 11, 14, 6]]
def orbitP5ActionColumns : Fin 5 → Fin 3 → ℕ :=
  ![![1, 2, 4], ![1, 2, 4], ![1, 2, 4], ![1, 2, 5], ![1, 2, 4]]
def orbitP5CorrectionColumns : Fin 5 → Fin 3 → ℕ :=
  ![![0, 0, 0], ![0, 0, 3598], ![0, 0, 5911], ![0, 0, 417], ![2903, 6966, 8023]]

def orbitP5RepresentativeCoeff (k : Fin 8) : Fin 3 → F2 :=
  coeffMask 3 (orbitP5RepresentativeMask (orbitP5Index k))
def orbitP5TargetCoeff (k : Fin 8) : Fin 3 → F2 :=
  coeffMask 3 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
