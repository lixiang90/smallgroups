/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent04Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,4)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP4RepresentativeMask : Fin 6 → ℕ :=
  ![0, 1, 2, 3, 4, 5]
def orbitP4Index : Fin 8 → Fin 6 :=
  ![0, 1, 2, 3, 4, 5, 5, 4]
def orbitP4AutPerm : Fin 5 → Fin 16 → Fin 16 :=
  ![![0, 5, 2, 3, 4, 6, 11, 12, 8, 9, 10, 1, 13, 15, 14, 7], ![0, 6, 2, 3, 4, 11, 1, 13, 8, 9, 10, 5, 15, 7, 14, 12], ![0, 1, 8, 3, 4, 11, 6, 7, 2, 14, 10, 5, 15, 13, 9, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11]]
def orbitP4AutInvPerm : Fin 5 → Fin 16 → Fin 16 :=
  ![![0, 11, 2, 3, 4, 1, 5, 15, 8, 9, 10, 6, 7, 12, 14, 13], ![0, 6, 2, 3, 4, 11, 1, 13, 8, 9, 10, 5, 15, 7, 14, 12], ![0, 1, 8, 3, 4, 11, 6, 7, 2, 14, 10, 5, 15, 13, 9, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11]]
def orbitP4ActionColumns : Fin 5 → Fin 3 → ℕ :=
  ![![1, 2, 4], ![1, 2, 4], ![1, 2, 4], ![1, 2, 4], ![1, 2, 7]]
def orbitP4CorrectionColumns : Fin 5 → Fin 3 → ℕ :=
  ![![65, 3755, 2762], ![6192, 2129, 5233], ![581, 4644, 5233], ![0, 0, 2714], ![0, 0, 45]]

def orbitP4RepresentativeCoeff (k : Fin 8) : Fin 3 → F2 :=
  coeffMask 3 (orbitP4RepresentativeMask (orbitP4Index k))
def orbitP4TargetCoeff (k : Fin 8) : Fin 3 → F2 :=
  coeffMask 3 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
