/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Reps
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart11

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents12 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [1, 0, 0, 0, 1], [1, 0, 0, 0, 0], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [1, 0, 1, 0, 1], [1, 0, 1, 0, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 1, 0, 0], [0, 0, 1, 1, 1], [0, 0, 1, 1, 0], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0], [1, 1, 1, 0, 1], [1, 1, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [0, 1, 0, 0, 1], [0, 1, 0, 0, 0], [1, 1, 0, 0, 0], [1, 1, 0, 0, 1]]
def generatedToGap12 (x : generatedGroup12) :
    PCGroup smallGroup_32_12 :=
  evalVec (gapExponents12 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_12.layers)

set_option maxHeartbeats 8000000 in -- finite verification of a 32-element isomorphism
noncomputable def generatedGapEquiv12 :
    generatedGroup12 ≃* PCGroup smallGroup_32_12 :=
  mulEquivOfDecide generatedToGap12 (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
