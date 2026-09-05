/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleSynthesis

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked H² basis cocycles for `SmallGroup(16,7)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def coverageP7HBasis : Fin 3 → ℕ := ![641338501601538798546202004328967884470729718869075066851799523, 1188417167050380993469256161024588911283362211027849147055660145, 8534046226223639110431127286610887935693564074229354365312573402]

theorem orbitP7_hbasis_cocycle (i : Fin 3) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent7Table (twoMask (coverageP7HBasis i))) := by
  fin_cases i <;> decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
