/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent07Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,7)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP7RepresentativeMask : Fin 6 → ℕ :=
  ![0, 1, 2, 4, 5, 6]
def orbitP7Index : Fin 8 → Fin 6 :=
  ![0, 1, 2, 2, 3, 4, 5, 5]
def orbitP7AutPerm : Fin 5 → Fin 16 → Fin 16 :=
  ![![0, 2, 1, 10, 4, 11, 14, 9, 13, 7, 3, 5, 15, 8, 6, 12], ![0, 6, 2, 10, 4, 15, 1, 13, 14, 9, 3, 12, 11, 7, 8, 5], ![0, 1, 8, 10, 4, 11, 13, 7, 2, 14, 3, 5, 15, 6, 9, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11]]
def orbitP7AutInvPerm : Fin 5 → Fin 16 → Fin 16 :=
  ![![0, 2, 1, 10, 4, 11, 14, 9, 13, 7, 3, 5, 15, 8, 6, 12], ![0, 6, 2, 10, 4, 15, 1, 13, 14, 9, 3, 12, 11, 7, 8, 5], ![0, 1, 8, 10, 4, 11, 13, 7, 2, 14, 3, 5, 15, 6, 9, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11]]
def orbitP7ActionColumns : Fin 5 → Fin 3 → ℕ :=
  ![![1, 3, 4], ![1, 2, 4], ![1, 2, 4], ![1, 2, 4], ![1, 2, 4]]
def orbitP7CorrectionColumns : Fin 5 → Fin 3 → ℕ :=
  ![![0, 0, 5592], ![0, 0, 6687], ![0, 0, 1049], ![0, 0, 3942], ![0, 0, 3783]]

def orbitP7RepresentativeCoeff (k : Fin 8) : Fin 3 → F2 :=
  coeffMask 3 (orbitP7RepresentativeMask (orbitP7Index k))
def orbitP7TargetCoeff (k : Fin 8) : Fin 3 → F2 :=
  coeffMask 3 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
