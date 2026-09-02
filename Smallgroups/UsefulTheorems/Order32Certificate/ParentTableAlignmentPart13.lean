/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.GAP.Polycyclic.Imported.Order16
import Smallgroups.UsefulTheorems.Order32Certificate.ParentTableAlignmentPart12

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked table-to-PC alignment for `SmallGroup(16,13)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent13GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent13TableToGap (x : CertifiedTableGroup parent13Table) :
    PCGroup smallGroup_16_13 :=
  evalVec (parent13GapExponents x.val) (pcGens smallGroup_16_13.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 16-element table isomorphism.
noncomputable def parent13TableGapEquiv :
    CertifiedTableGroup parent13Table ≃* PCGroup smallGroup_16_13 :=
  mulEquivOfDecide parent13TableToGap
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
