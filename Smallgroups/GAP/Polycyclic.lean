/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.CyclicExtension
import Smallgroups.GAP.Polycyclic.Basic
import Smallgroups.GAP.Polycyclic.PresentationHom

/-!
# Polycyclic (pc) groups

Umbrella file for the polycyclic group framework:

* `Polycyclic/CyclicExtension.lean` — cyclic extensions `1 → G → CycExt data → C_r → 1`
  from the data `(f, a, r)` (a bare function `f` and the power element `a`), with
  consistency `CycExtData.Consistent` decidable by `decide`.
* `Polycyclic/Basic.lean` — pc presentations (`PCLayer`/`PCPres`), the tower
  construction `PCGroup`, normal-form bijection `pcTuple`,
  `card_PCGroup : Nat.card (PCGroup p) = ∏ rᵢ`, and the `mulEquivOfDecide` tool.
-/
