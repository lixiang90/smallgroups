/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleSynthesis

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked H² basis cocycles for `SmallGroup(16,1)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def coverageP1HBasis : Fin 1 → ℕ := ![1645655236882844667277692944970034326974182713323418372769054719]

theorem orbitP1_hbasis_cocycle (i : Fin 1) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent1Table (twoMask (coverageP1HBasis i))) := by
  fin_cases i
  decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
