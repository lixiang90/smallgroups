/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent08Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Core

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,8)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP8RepresentativeMask : Fin 4 → ℕ :=
  ![0, 1, 2, 3]
def orbitP8Index : Fin 4 → Fin 4 :=
  ![0, 1, 2, 3]
def orbitP8AutPerm : Fin 4 → Fin 16 → Fin 16 :=
  ![![0, 6, 2, 10, 4, 15, 1, 13, 14, 9, 3, 12, 11, 7, 8, 5], ![0, 1, 8, 10, 4, 11, 13, 7, 2, 14, 3, 5, 15, 6, 9, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11]]
def orbitP8AutInvPerm : Fin 4 → Fin 16 → Fin 16 :=
  ![![0, 6, 2, 10, 4, 15, 1, 13, 14, 9, 3, 12, 11, 7, 8, 5], ![0, 1, 8, 10, 4, 11, 13, 7, 2, 14, 3, 5, 15, 6, 9, 12], ![0, 7, 2, 3, 4, 12, 13, 1, 8, 9, 10, 15, 5, 6, 14, 11], ![0, 1, 9, 3, 4, 12, 6, 7, 14, 2, 10, 15, 5, 13, 8, 11]]
def orbitP8ActionColumns : Fin 4 → Fin 2 → ℕ :=
  ![![1, 2], ![1, 2], ![1, 2], ![1, 2]]
def orbitP8CorrectionColumns : Fin 4 → Fin 2 → ℕ :=
  ![![0, 0], ![0, 0], ![0, 0], ![0, 0]]

def orbitP8RepresentativeCoeff (k : Fin 4) : Fin 2 → F2 :=
  coeffMask 2 (orbitP8RepresentativeMask (orbitP8Index k))
def orbitP8TargetCoeff (k : Fin 4) : Fin 2 → F2 :=
  coeffMask 2 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
