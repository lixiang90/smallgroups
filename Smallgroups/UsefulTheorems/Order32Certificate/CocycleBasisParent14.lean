/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleSynthesis

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Kernel-checked H² basis cocycles for `SmallGroup(16,14)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def parent14HBasis : Fin 10 → ℕ := ![166686425445096357569464344780766026156924702837178368, 273601455907355132374120767948227063136366305162035200, 469612345088162886182657543755238964265342576090939392, 853402695032736598364201991923299012145175379537035264, 8965098922415103627162783123176034981463446742176768000000, 15387787740165821456468633391420609786132387818495201280000, 27963446160223657416211846777537283813121967983675125760000, 462046927505425427379554428217599293265436691214861696473768945, 868501819075218813779095707357791259455107130016393930265084815, 27168971446040215891358956329227877113926338971524287503521238211599]

theorem orbitP14_hbasis_cocycle (i : Fin 10) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent14Table (twoMask (parent14HBasis i))) := by
  fin_cases i <;> decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
