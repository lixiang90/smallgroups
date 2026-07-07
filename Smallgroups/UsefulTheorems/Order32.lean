/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32.Common
import Smallgroups.UsefulTheorems.Order32.GenericTools
import Smallgroups.UsefulTheorems.Order32.G6
import Smallgroups.UsefulTheorems.Order32.G1
import Smallgroups.UsefulTheorems.Order32.G13
import Smallgroups.UsefulTheorems.Order32.G7
import Smallgroups.UsefulTheorems.Order32.G0
import Smallgroups.UsefulTheorems.Order32.G12
import Smallgroups.UsefulTheorems.Order32.G2
import Smallgroups.UsefulTheorems.Order32.G3
import Smallgroups.UsefulTheorems.Order32.G4
import Smallgroups.UsefulTheorems.Order32.G8
import Smallgroups.UsefulTheorems.Order32.G9
import Smallgroups.UsefulTheorems.Order32.G10
import Smallgroups.UsefulTheorems.Order32.G5
import Smallgroups.UsefulTheorems.Order32.G11

/-!
# Classification of groups of order 32 via the p-group generation algorithm

This file applies the generic p-group generation machinery
(`Smallgroups.UsefulTheorems.PGroupGeneration`) to classify groups of order
`32 = 2 ^ 5` as central extensions by `C₂` of the 14 known representatives of order
`16 = 2 ^ 4` (`order16_wild_reps`, from `Order16_Wild.lean`).

## The reduction step

Any `G` with `Nat.card G = 32` has (`order_prime_pow_central_reduction`) a central
element `z` of order `2` with `⟨z⟩` normal and `Nat.card (G ⧸ ⟨z⟩) = 16`.  By
`order16_wild_classification`, `G ⧸ ⟨z⟩ ≃* order16_wild_reps i` for some `i : Fin 14`.
Reconstruction (`cocycleGroup_reconstruction_of_quotient_iso`) then produces a normalized
`2`-cocycle `f : order16_wild_reps i → order16_wild_reps i → ZMod 2` with
`G ≃* CocycleGroup f hf`.

`order32_central_reduction` (in `Order32/Common.lean`) bundles this: every group of order
32 is (isomorphic to) some `CocycleGroup f hf` over some `order16_wild_reps i`.  The
remaining work — enumerating the cocycles over each of the 14 quotients up to the
`Equivalences.lean` moves, and proving distinctness of the survivors — is carried out
parent-by-parent in the `Order32/G*.lean` files:

* `Order32/GenericTools.lean` — reusable tools for `SemidirectProduct`-shaped parents.
* `Order32/G6.lean` — cyclic `C₁₆`.
* `Order32/G1.lean`, `G13.lean`, `G7.lean`, `G0.lean` — abelian-quotient parents
  (`C₈×C₂`, `C₄×C₄`, `K₈×C₂`, `(C₂)⁴`), abelian-lift branches.
* `Order32/G12.lean`, `G2.lean`, `G3.lean`, `G4.lean`, `G8.lean`, `G9.lean`, `G10.lean`,
  `G5.lean`, `G11.lean` — the remaining non-abelian parents (`C₄⋊C₄`, the three
  `C₈⋊C₂` groups, the three `K₈⋊C₂` groups, `Q₁₆`, `Q₈×C₂`), trivial-cocycle branches
  (plus, in `G2.lean`, the first "doubled generator" branch).
-/
