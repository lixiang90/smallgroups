/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeOrderClassification
import Smallgroups.UsefulTheorems.Counting
import Mathlib.Tactic.NormNum.Prime

/-!
# GAP-numbered representatives: order `1` and prime orders

This file starts the correspondence between the project's classifications and the
**GAP SmallGroups library** numbering.  For each order `N` with `k` isomorphism classes,
the GAP-numbered representative list is a function `Fin k → Type` where the index
`⟨j - 1, _⟩` corresponds to `SmallGroup(N, j)`.

* `order1GapRep` — the unique class `SmallGroup(1, 1)`, the trivial group.
* `primeGapRep p` — the unique class `SmallGroup(p, 1)` for `p` prime, the cyclic group
  `ℤ/p`.

Both lists come with exhaustiveness (`*_gap_classification`) and the bundled
`IsClassif` statement (`*_gap_isClassif`), reusing the `PrimeOrderClassification`
engine.
-/

namespace Smallgroups.GAP

open Smallgroups.UsefulTheorems

/-! ## Order `1` -/

/-- The GAP SmallGroups representative list for order `1`: the single class
`SmallGroup(1, 1)` is the trivial group, represented by `CyclicRep 1 = ℤ/1`. -/
abbrev order1GapRep : Fin 1 → Type := rep1 (CyclicRep 1)

/-- `SmallGroup(1, 1)` has order `1`. -/
theorem card_order1GapRep (i : Fin 1) : Nat.card (order1GapRep i) = 1 :=
  card_cyclicRep one_ne_zero

/-- **Exhaustiveness (GAP numbering).** Every group of order `1` is isomorphic to
`SmallGroup(1, 1)`. -/
theorem order1_gap_classification (G : Type) [Group G] (hG : Nat.card G = 1) :
    ∃ i : Fin 1, Nonempty (G ≃* order1GapRep i) :=
  haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hG).1
  ⟨0, cyclicRep_classification one_ne_zero hG⟩

/-- **Counting (GAP numbering).** The GAP list for order `1` is a complete,
non-redundant representative list. -/
theorem order1_gap_isClassif : IsClassif 1 order1GapRep :=
  isClassif_one _ (card_cyclicRep one_ne_zero) (fun G _ hG =>
    haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hG).1
    cyclicRep_classification one_ne_zero hG)

/-! ## Prime orders -/

/-- The GAP SmallGroups representative list for a prime order `p`: the single class
`SmallGroup(p, 1)` is the cyclic group `ℤ/p`, represented by `CyclicRep p`. -/
abbrev primeGapRep (p : ℕ) : Fin 1 → Type := rep1 (CyclicRep p)

/-- `SmallGroup(p, 1)` has order `p`. -/
theorem card_primeGapRep (p : ℕ) [NeZero p] (i : Fin 1) : Nat.card (primeGapRep p i) = p :=
  card_cyclicRep (NeZero.ne p)

/-- **Exhaustiveness (GAP numbering).** Every group of prime order `p` is isomorphic to
`SmallGroup(p, 1) = ℤ/p`. -/
theorem prime_gap_classification (hp : Nat.Prime p) {G : Type} [Group G]
    (hG : Nat.card G = p) : ∃ i : Fin 1, Nonempty (G ≃* primeGapRep p i) :=
  ⟨0, prime_classification hp hG⟩

/-- **Counting (GAP numbering).** The GAP list for a prime order `p` is a complete,
non-redundant representative list. -/
theorem prime_gap_isClassif (hp : Nat.Prime p) : IsClassif p (primeGapRep p) :=
  isClassif_one _ (card_cyclicRep hp.pos.ne') (fun _G _ hG => prime_classification hp hG)

end Smallgroups.GAP
