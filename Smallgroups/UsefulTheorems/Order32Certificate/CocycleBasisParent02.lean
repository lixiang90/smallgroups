/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleSynthesis

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked H² basis cocycles for `SmallGroup(16,2)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def coverageP2HBasis : Fin 3 → ℕ := ![154875521659934869304647767775278009491769860428814156225188225, 848306407930016989821231158326604719525683044176528247044861983, 37854089034732381634408922147660728465545643726412478319535587323]

theorem orbitP2_hbasis_cocycle (i : Fin 3) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent2Table (twoMask (coverageP2HBasis i))) := by
  fin_cases i <;> decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
