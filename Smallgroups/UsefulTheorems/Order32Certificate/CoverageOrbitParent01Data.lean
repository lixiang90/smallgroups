/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageLinearParent01Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction
import Smallgroups.UsefulTheorems.Order32Certificate.Parent14OrbitAlignmentPart07

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated compositional orbit data for `SmallGroup(16,1)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP1RepresentativeMask : Fin 2 → ℕ :=
  ![0, 1]
def orbitP1Index : Fin 2 → Fin 2 :=
  ![0, 1]
def orbitP1AutPerm : Fin 2 → Fin 16 → Fin 16 :=
  ![![0, 15, 14, 10, 4, 13, 12, 11, 9, 8, 3, 7, 6, 5, 2, 1], ![0, 6, 9, 3, 4, 15, 7, 13, 14, 2, 10, 5, 11, 1, 8, 12]]
def orbitP1AutInvPerm : Fin 2 → Fin 16 → Fin 16 :=
  ![![0, 15, 14, 10, 4, 13, 12, 11, 9, 8, 3, 7, 6, 5, 2, 1], ![0, 13, 9, 3, 4, 11, 1, 6, 14, 2, 10, 12, 15, 7, 8, 5]]
def orbitP1ActionColumns : Fin 2 → Fin 1 → ℕ :=
  ![![1], ![1]]
def orbitP1CorrectionColumns : Fin 2 → Fin 1 → ℕ :=
  ![![9102], ![2980]]

def orbitP1RepresentativeCoeff (k : Fin 2) : Fin 1 → F2 :=
  coeffMask 1 (orbitP1RepresentativeMask (orbitP1Index k))
def orbitP1TargetCoeff (k : Fin 2) : Fin 1 → F2 :=
  coeffMask 1 k.val

end Smallgroups.UsefulTheorems.Order32Certificate
