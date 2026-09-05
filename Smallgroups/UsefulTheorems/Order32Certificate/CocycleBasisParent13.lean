/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleSynthesis

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked H² basis cocycles for `SmallGroup(16,13)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def coverageP13HBasis : Fin 5 → ℕ := ![10675689723925065914906850550499541562929110139700759953408, 16804326417289455606797820310971500608314340034714159185920, 27964299510832712855197430662498583821241382819282194497536, 64182939602736797167269451130512795715371598005951401947378973, 27985106405855118900743278575382036045269923724176478663315552663294]

theorem orbitP13_hbasis_cocycle (i : Fin 5) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent13Table (twoMask (coverageP13HBasis i))) := by
  fin_cases i <;> decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
