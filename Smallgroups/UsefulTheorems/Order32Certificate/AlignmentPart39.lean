/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Reps
import Smallgroups.GAP.Polycyclic.Imported.Order32
import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart38

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.GAP

def gapExponents39 : Fin 32 → List ℕ := ![[0, 0, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 1, 1], [1, 0, 0, 1, 1], [0, 1, 1, 1, 1], [0, 1, 0, 1, 1], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 1, 0, 1], [1, 1, 0, 0, 0], [1, 1, 1, 0, 0], [1, 0, 1, 0, 0], [1, 0, 0, 0, 0], [1, 0, 1, 1, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0], [0, 1, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 1, 1, 1], [1, 1, 0, 1, 0], [1, 1, 1, 1, 0], [1, 1, 0, 0, 1], [1, 1, 1, 0, 1], [1, 0, 1, 0, 1], [1, 0, 0, 0, 1], [0, 1, 1, 0, 1], [0, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 1, 1, 1]]
def generatedToGap39 (x : generatedGroup39) :
    PCGroup smallGroup_32_39 :=
  evalVec (gapExponents39 (certifiedExtensionIndex x))
    (pcGens smallGroup_32_39.layers)

set_option maxHeartbeats 8000000 in -- finite verification of a 32-element isomorphism
noncomputable def generatedGapEquiv39 :
    generatedGroup39 ≃* PCGroup smallGroup_32_39 :=
  mulEquivOfDecide generatedToGap39 (by decide +kernel) (by decide +kernel)

end Smallgroups.UsefulTheorems.Order32Certificate
