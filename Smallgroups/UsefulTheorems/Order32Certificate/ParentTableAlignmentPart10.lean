/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.GAP.Polycyclic.Imported.Order16
import Smallgroups.UsefulTheorems.Order32Certificate.ParentTableAlignmentPart09

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked table-to-PC alignment for `SmallGroup(16,10)`. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def parent10GapExponents : Fin 16 → List ℕ := ![[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [1, 1, 0, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 0], [1, 1, 0, 1], [1, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]
def parent10TableToGap (x : CertifiedTableGroup parent10Table) :
    PCGroup smallGroup_16_10 :=
  evalVec (parent10GapExponents x.val) (pcGens smallGroup_16_10.layers)

set_option maxHeartbeats 8000000 in
-- Finite verification of the generated 16-element table isomorphism.
noncomputable def parent10TableGapEquiv :
    CertifiedTableGroup parent10Table ≃* PCGroup smallGroup_16_10 :=
  mulEquivOfDecide parent10TableToGap
    (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
