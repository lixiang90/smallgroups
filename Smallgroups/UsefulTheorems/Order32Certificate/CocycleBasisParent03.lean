/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleSynthesis

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked H² basis cocycles for `SmallGroup(16,3)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def coverageP3HBasis : Fin 4 → ℕ := ![19886466143093925718013356981690295991480775548709087375393164, 139556785305305502546850528553532350514450179199160910361758427, 497613594432573823048620340081730535532523228573592935017916085, 87218584561362305858687744298010276208478497949166363414934112712]

theorem orbitP3_hbasis_cocycle (i : Fin 4) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent3Table (twoMask (coverageP3HBasis i))) := by
  fin_cases i <;> decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
