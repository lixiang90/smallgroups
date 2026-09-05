/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleSynthesis

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked H² basis cocycles for `SmallGroup(16,9)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def coverageP9HBasis : Fin 2 → ℕ := ![641338501601538798546202004328967884470729718869075066851799523, 1188417167050380993469256161024588911283362211027849147055660145]

theorem orbitP9_hbasis_cocycle (i : Fin 2) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent9Table (twoMask (coverageP9HBasis i))) := by
  fin_cases i <;> decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
