/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.PGroupGeneration.Frattini
import Smallgroups.UsefulTheorems.SemidirectProductClassify
import Smallgroups.UsefulTheorems.Order32.Common
import Smallgroups.UsefulTheorems.Order32.GenericTools
import Smallgroups.UsefulTheorems.Order32.G0
import Smallgroups.UsefulTheorems.Order32.G1
import Smallgroups.UsefulTheorems.Order32.G2
import Smallgroups.UsefulTheorems.Order32.G3
import Smallgroups.UsefulTheorems.Order32.G4
import Smallgroups.UsefulTheorems.Order32.G5
import Smallgroups.UsefulTheorems.Order32.G6
import Smallgroups.UsefulTheorems.Order32.G7
import Smallgroups.UsefulTheorems.Order32.G8
import Smallgroups.UsefulTheorems.Order32.G9
import Smallgroups.UsefulTheorems.Order32.G10
import Smallgroups.UsefulTheorems.Order32.G11
import Smallgroups.UsefulTheorems.Order32.G12
import Smallgroups.UsefulTheorems.Order32.G13

/-!
# Order 32: pairwise distinctness of the constructed representatives

**Partial result.** Across `Order32/G0.lean`–`G13.lean`, 36 concrete order-32 groups have
been constructed as descendants of the 14 order-16 parents. Of these, 4 pairs turn out
to be literally the same Lean type (the same abelian group of order 32 is genuinely
reachable as a central extension of two different order-16 quotients), and one further
pair (`G1`'s `C₈×C₄` and `G13`'s `C₄×C₈`) is isomorphic via a plain `Prod.swap` despite
being different Lean types — leaving 31 candidate concrete types. This file proves a
**25-member subfamily** pairwise non-isomorphic. This is NOT yet `IsClassif 32` — four
constructed candidates remain parked in unresolved ties, and many cocycle-bit branches
remain unconstructed; the full classification has 51 classes.

The dropped duplicates (kept under the lower-numbered parent):
* `G0`'s `C₄×C₂×C₂×C₂` branch = `G7`'s 3rd branch (`G0.lean:40`, `G7.lean:37-38`).
* `G1`'s `C₁₆×C₂` branch = `G6`'s 2nd branch (`G1.lean:30`, `G6.lean:27`).
* `G1`'s `C₈×C₂×C₂` branch = `G7`'s 1st branch (`G1.lean:32`, `G7.lean:34`).
* `G7`'s `C₄×C₄×C₂` branch = `G13`'s 2nd branch (`G7.lean:35-36`, `G13.lean:31-32`).
* `G13`'s `C₄×C₈` branch ≅ `G1`'s `C₈×C₄` branch (isomorphic, not literally equal).

## Method

* The **7 abelian** representatives are separated by the standard finite-abelian
  invariant `(pow_eq_one_card _ 2, _ 4, _ 8, _ 16)` (element-order-divisor counts).
* The **24 non-abelian** representatives (9 of shape `Qᵢ × C₂` for a known order-16
  parent `Qᵢ`, plus 15 genuinely new order-32-specific groups) are separated by the
  5-tuple `(|Z(·)|, pow_eq_one_card _ 2, _ 4, _ 8, sq_image_card _)`, reusing the
  already-generic, already-`MulEquiv`-invariant building blocks from `Order16_Wild.lean`
  and `CenterInvariant.lean` (the same recipe that separated the 14 order-16 groups,
  including the hardest pair there). Where this 5-tuple does not separate a pair, the
  newly-added `Nat.card (frattini ·)` invariant (`PGroupGeneration/Frattini.lean`,
  `frattini_card_eq_of_mulEquiv`) is appended as a 6th coordinate — this is the one place
  the p-group-generation Frattini toolkit is actually invoked for distinctness.
* One formerly tied pair is separated by the kernel-checked count of commuting ordered
  pairs `(x,y)` satisfying `x²=1` and `y⁴=1` (256 versus 192).
-/

namespace Smallgroups.UsefulTheorems

/-! ### The 32 deduplicated representatives -/

/-- The 7 abelian representatives constructed in `G0/G1/G6/G7/G13`. Besides the 3
literal-type duplicates among these branches (`G6`'s 2nd branch = `G1`'s 1st, `G7`'s 1st
= `G1`'s 3rd, `G7`'s 2nd = `G13`'s 2nd — all already dropped below), `G1`'s `C₈×C₄`
branch and `G13`'s `C₄×C₈` branch are also isomorphic (as abstract groups, via
`Prod.swap` — literally the same group with its two cyclic factors listed in the other
order) even though they are different Lean types; only `G1`'s copy is kept. -/
noncomputable abbrev order32_abelian_reps : Fin 7 → Type
  | 0 => Multiplicative (ZMod 32)                                            -- G6
  | 1 => Multiplicative (ZMod 16) × Multiplicative (ZMod 2)                  -- G1 (= G6 dup)
  | 2 => C8g × Multiplicative (ZMod 4)                                       -- G1 (= G13's C4×C8)
  | 3 => C8g × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)             -- G1 (= G7 dup)
  | 4 => Multiplicative (ZMod 4) × Multiplicative (ZMod 4)
      × Multiplicative (ZMod 2)                                              -- G7 (= G13 dup)
  | 5 => Multiplicative (ZMod 4) × Multiplicative (ZMod 2)
      × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)                    -- G0 (= G7 dup)
  | 6 => Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
      × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)                    -- G0

noncomputable instance instGroupOrder32AbelianReps : ∀ i, Group (order32_abelian_reps i)
  | 0 => inferInstanceAs (Group (Multiplicative (ZMod 32)))
  | 1 => inferInstanceAs (Group (Multiplicative (ZMod 16) × Multiplicative (ZMod 2)))
  | 2 => inferInstanceAs (Group (C8g × Multiplicative (ZMod 4)))
  | 3 => inferInstanceAs (Group (C8g × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
  | 4 => inferInstanceAs (Group (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)
      × Multiplicative (ZMod 2)))
  | 5 => inferInstanceAs (Group (Multiplicative (ZMod 4) × Multiplicative (ZMod 2)
      × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
  | 6 => inferInstanceAs (Group (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)
      × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))

theorem card_order32_abelian_reps (i : Fin 7) : Nat.card (order32_abelian_reps i) = 32 := by
  fin_cases i <;>
    simp [order32_abelian_reps, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

/-! ### Distinctness of the abelian representatives -/

/-- The element-order-divisor-count tuple `(pow_eq_one_card _ 2, _ 4, _ 8, _ 16)` — a
standard isomorphism invariant separating all abelian groups of order 32. -/
noncomputable def order32AbelianInvariant (H : Type*) [Group H] : ℕ × ℕ × ℕ × ℕ :=
  (pow_eq_one_card H 2, pow_eq_one_card H 4, pow_eq_one_card H 8, pow_eq_one_card H 16)

theorem order32AbelianInvariant_eq_of_mulEquiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) : order32AbelianInvariant H = order32AbelianInvariant K := by
  simp only [order32AbelianInvariant, pow_eq_one_card_eq_of_mulEquiv 2 e,
    pow_eq_one_card_eq_of_mulEquiv 4 e, pow_eq_one_card_eq_of_mulEquiv 8 e,
    pow_eq_one_card_eq_of_mulEquiv 16 e]

/-- Helper: establish the invariant tuple by four `Fintype.card` computations. -/
theorem order32AbelianInvariant_eq_of_counts {H : Type*} [Group H]
    [Fintype {x : H // x ^ 2 = 1}] [Fintype {x : H // x ^ 4 = 1}]
    [Fintype {x : H // x ^ 8 = 1}] [Fintype {x : H // x ^ 16 = 1}]
    {a b c d : ℕ}
    (h1 : Fintype.card {x : H // x ^ 2 = 1} = a)
    (h2 : Fintype.card {x : H // x ^ 4 = 1} = b)
    (h3 : Fintype.card {x : H // x ^ 8 = 1} = c)
    (h4 : Fintype.card {x : H // x ^ 16 = 1} = d) :
    order32AbelianInvariant H = (a, b, c, d) := by
  simp only [order32AbelianInvariant, pow_eq_one_card, Nat.card_eq_fintype_card, h1, h2, h3, h4]

set_option maxHeartbeats 1000000 in -- large finite decide over concrete order-32 group elements
private theorem abelian_invariant_0 : order32AbelianInvariant (order32_abelian_reps 0)
    = (2, 4, 8, 16) := by
  exact order32AbelianInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in -- large finite decide over concrete order-32 group elements
private theorem abelian_invariant_1 : order32AbelianInvariant (order32_abelian_reps 1)
    = (4, 8, 16, 32) := by
  exact order32AbelianInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in -- large finite decide over concrete order-32 group elements
private theorem abelian_invariant_2 : order32AbelianInvariant (order32_abelian_reps 2)
    = (4, 16, 32, 32) := by
  exact order32AbelianInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in -- large finite decide over concrete order-32 group elements
private theorem abelian_invariant_3 : order32AbelianInvariant (order32_abelian_reps 3)
    = (8, 16, 32, 32) := by
  exact order32AbelianInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in -- large finite decide over concrete order-32 group elements
private theorem abelian_invariant_4 : order32AbelianInvariant (order32_abelian_reps 4)
    = (8, 32, 32, 32) := by
  exact order32AbelianInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in -- large finite decide over concrete order-32 group elements
private theorem abelian_invariant_5 : order32AbelianInvariant (order32_abelian_reps 5)
    = (16, 32, 32, 32) := by
  exact order32AbelianInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in -- large finite decide over concrete order-32 group elements
private theorem abelian_invariant_6 : order32AbelianInvariant (order32_abelian_reps 6)
    = (32, 32, 32, 32) := by
  exact order32AbelianInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private def order32_abelian_invariant_table : Fin 7 → ℕ × ℕ × ℕ × ℕ
  | 0 => (2, 4, 8, 16)
  | 1 => (4, 8, 16, 32)
  | 2 => (4, 16, 32, 32)
  | 3 => (8, 16, 32, 32)
  | 4 => (8, 32, 32, 32)
  | 5 => (16, 32, 32, 32)
  | 6 => (32, 32, 32, 32)

private theorem order32_abelian_invariant_spec (i : Fin 7) :
    order32AbelianInvariant (order32_abelian_reps i) = order32_abelian_invariant_table i := by
  fin_cases i
  exacts [abelian_invariant_0, abelian_invariant_1, abelian_invariant_2, abelian_invariant_3,
    abelian_invariant_4, abelian_invariant_5, abelian_invariant_6]

theorem order32_abelian_reps_pairwise : PairwiseNonMulEquiv order32_abelian_reps := by
  apply PairwiseNonMulEquiv.of_invariant order32_abelian_invariant_table
  · intro i j ⟨e⟩
    rw [← order32_abelian_invariant_spec i, ← order32_abelian_invariant_spec j]
    exact order32AbelianInvariant_eq_of_mulEquiv e
  · intro i j hij _
    have hinj : Function.Injective order32_abelian_invariant_table := by decide
    exact hinj hij

/-- The 9 non-abelian "trivial cocycle" representatives, `Qᵢ × C₂` for a known order-16
parent `Qᵢ`. -/
noncomputable abbrev order32_trivial_reps : Fin 9 → Type
  | 0 => order16_wild_G2 × Multiplicative (ZMod 2)
  | 1 => order16_wild_G3 × Multiplicative (ZMod 2)
  | 2 => order16_wild_G4 × Multiplicative (ZMod 2)
  | 3 => order16_wild_G5 × Multiplicative (ZMod 2)
  | 4 => order16_wild_G8 × Multiplicative (ZMod 2)
  | 5 => order16_wild_G9 × Multiplicative (ZMod 2)
  | 6 => order16_wild_G10 × Multiplicative (ZMod 2)
  | 7 => order16_wild_G11 × Multiplicative (ZMod 2)
  | 8 => order16_wild_G12 × Multiplicative (ZMod 2)

noncomputable instance instGroupOrder32TrivialReps : ∀ i, Group (order32_trivial_reps i)
  | 0 => inferInstanceAs (Group (order16_wild_G2 × Multiplicative (ZMod 2)))
  | 1 => inferInstanceAs (Group (order16_wild_G3 × Multiplicative (ZMod 2)))
  | 2 => inferInstanceAs (Group (order16_wild_G4 × Multiplicative (ZMod 2)))
  | 3 => inferInstanceAs (Group (order16_wild_G5 × Multiplicative (ZMod 2)))
  | 4 => inferInstanceAs (Group (order16_wild_G8 × Multiplicative (ZMod 2)))
  | 5 => inferInstanceAs (Group (order16_wild_G9 × Multiplicative (ZMod 2)))
  | 6 => inferInstanceAs (Group (order16_wild_G10 × Multiplicative (ZMod 2)))
  | 7 => inferInstanceAs (Group (order16_wild_G11 × Multiplicative (ZMod 2)))
  | 8 => inferInstanceAs (Group (order16_wild_G12 × Multiplicative (ZMod 2)))

theorem card_order32_trivial_reps (i : Fin 9) : Nat.card (order32_trivial_reps i) = 32 := by
  have hc2 : Fintype.card (Multiplicative (ZMod 2)) = 2 := by
    simp [Fintype.card_multiplicative, ZMod.card]
  have hg2 : Fintype.card order16_wild_G2 = 16 := by
    rw [← Nat.card_eq_fintype_card]; exact card_order16_wild_G2
  have hg3 : Fintype.card order16_wild_G3 = 16 := by
    rw [← Nat.card_eq_fintype_card]; exact card_order16_wild_G3
  have hg4 : Fintype.card order16_wild_G4 = 16 := by
    rw [← Nat.card_eq_fintype_card]; exact card_order16_wild_G4
  have hg5 : Fintype.card order16_wild_G5 = 16 := by
    rw [← Nat.card_eq_fintype_card]; exact card_order16_wild_G5
  have hg8 : Fintype.card order16_wild_G8 = 16 := by
    rw [← Nat.card_eq_fintype_card]; exact card_order16_wild_G8
  have hg9 : Fintype.card order16_wild_G9 = 16 := by
    rw [← Nat.card_eq_fintype_card]; exact card_order16_wild_G9
  have hg10 : Fintype.card order16_wild_G10 = 16 := by
    rw [← Nat.card_eq_fintype_card]; exact card_order16_wild_G10
  have hg11 : Fintype.card order16_wild_G11 = 16 := by
    rw [← Nat.card_eq_fintype_card]; exact card_order16_wild_G11
  have hg12 : Fintype.card order16_wild_G12 = 16 := by
    rw [← Nat.card_eq_fintype_card]; exact card_order16_wild_G12
  fin_cases i <;>
    simp [order32_trivial_reps, hc2, hg2, hg3, hg4, hg5, hg8, hg9, hg10, hg11, hg12]

/-! ### Distinctness of the `Qᵢ × C₂` representatives

The 9 `order16_wild_Gᵢ` parents used here are already known pairwise non-isomorphic
(`order16_wild_pairwise_noniso`), via the tuple `(|Z(Qᵢ)|, pow_eq_one_card _ 2,
pow_eq_one_card _ 4, sq_image_card _)`. Each of these coordinates is multiplicative over a
direct product (`card_center_prod`, and the two new lemmas below), and `C₂`'s own
coordinates are trivial constants, so the *same* tuple doubled/left-alone
(`(2|Z(Qᵢ)|, 2·pow2(Qᵢ), 2·pow4(Qᵢ), sq_image(Qᵢ))`) separates the 9 `Qᵢ × C₂`
representatives — computed directly on the smaller (16-element) `Qᵢ` factor rather than
on the 32-element product, for speed. -/

theorem pow_eq_one_card_prod (H K : Type*) [Group H] [Group K] (n : ℕ) :
    pow_eq_one_card (H × K) n = pow_eq_one_card H n * pow_eq_one_card K n := by
  unfold pow_eq_one_card
  rw [← Nat.card_prod]
  refine Nat.card_congr ⟨fun p => (⟨p.1.1, ?_⟩, ⟨p.1.2, ?_⟩), fun p => ⟨(p.1.1, p.2.1), ?_⟩,
    fun p => by ext <;> rfl, fun p => by ext <;> rfl⟩
  · have h := p.2; rw [Prod.pow_mk] at h; exact congrArg Prod.fst h
  · have h := p.2; rw [Prod.pow_mk] at h; exact congrArg Prod.snd h
  · rw [Prod.pow_mk]; exact Prod.ext p.1.2 p.2.2

theorem sq_image_card_prod (H K : Type*) [Group H] [Group K] :
    sq_image_card (H × K) = sq_image_card H * sq_image_card K := by
  unfold sq_image_card
  rw [← Nat.card_prod]
  refine Nat.card_congr ⟨fun z => (⟨z.1.1, ?_⟩, ⟨z.1.2, ?_⟩), fun z => ⟨(z.1.1, z.2.1), ?_⟩,
    fun z => by ext <;> rfl, fun z => by ext <;> rfl⟩
  · obtain ⟨p, hp⟩ := z.2; exact ⟨p.1, by rw [← hp, Prod.pow_mk]⟩
  · obtain ⟨p, hp⟩ := z.2; exact ⟨p.2, by rw [← hp, Prod.pow_mk]⟩
  · obtain ⟨x, hx⟩ := z.1.2; obtain ⟨y, hy⟩ := z.2.2
    exact ⟨(x, y), by rw [Prod.pow_mk, hx, hy]⟩

theorem card_c2_pow_eq_one (n : ℕ) (hn : 2 ∣ n) :
    pow_eq_one_card (Multiplicative (ZMod 2)) n = 2 := by
  have : Fintype.card {x : Multiplicative (ZMod 2) // x ^ n = 1} = 2 := by
    obtain ⟨k, rfl⟩ := hn
    have hpow : ∀ x : Multiplicative (ZMod 2), x ^ (2 * k) = 1 := by
      intro x; rw [pow_mul]
      have : x ^ 2 = 1 := by revert x; decide
      rw [this, one_pow]
    simp [Fintype.card_congr (Equiv.subtypeUnivEquiv (fun x => hpow x)),
      Fintype.card_multiplicative, ZMod.card]
  unfold pow_eq_one_card
  rw [Nat.card_eq_fintype_card]
  exact this

theorem card_c2_sq_image : sq_image_card (Multiplicative (ZMod 2)) = 1 := by
  have : ∀ y : Multiplicative (ZMod 2), (∃ x, x ^ 2 = y) ↔ y = 1 := by decide
  unfold sq_image_card
  rw [Nat.card_eq_fintype_card]
  simp only [this]
  exact Fintype.card_eq_one_iff.mpr ⟨⟨1, rfl⟩, fun a => Subtype.ext a.2⟩

/-- The invariant tuple `(|Z(H)|, pow_eq_one_card _ 2, _ 4, sq_image_card _)`, the same
4-coordinate invariant already known to separate the 14 `order16_wild` representatives. -/
noncomputable def order32TrivialInvariant (H : Type*) [Group H] : ℕ × ℕ × ℕ × ℕ :=
  (Nat.card (Subgroup.center H), pow_eq_one_card H 2, pow_eq_one_card H 4, sq_image_card H)

theorem order32TrivialInvariant_eq_of_mulEquiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) : order32TrivialInvariant H = order32TrivialInvariant K := by
  simp only [order32TrivialInvariant, card_center_eq_of_mulEquiv e,
    pow_eq_one_card_eq_of_mulEquiv 2 e, pow_eq_one_card_eq_of_mulEquiv 4 e,
    sq_image_card_eq_of_mulEquiv e]

/-- Helper: establish the invariant tuple by four `Fintype.card` computations. -/
theorem order32TrivialInvariant_eq_of_counts {H : Type*} [Group H]
    [Fintype (Subgroup.center H)] [Fintype {x : H // x ^ 2 = 1}] [Fintype {x : H // x ^ 4 = 1}]
    [Fintype {y : H // ∃ x : H, x ^ 2 = y}]
    {a b c d : ℕ}
    (h1 : Fintype.card (Subgroup.center H) = a)
    (h2 : Fintype.card {x : H // x ^ 2 = 1} = b)
    (h3 : Fintype.card {x : H // x ^ 4 = 1} = c)
    (h4 : Fintype.card {y : H // ∃ x : H, x ^ 2 = y} = d) :
    order32TrivialInvariant H = (a, b, c, d) := by
  simp only [order32TrivialInvariant, pow_eq_one_card, sq_image_card, Nat.card_eq_fintype_card,
    h1, h2, h3, h4]

/-- `order32TrivialInvariant` is multiplicative over direct products. -/
theorem order32TrivialInvariant_prod (H K : Type*) [Group H] [Group K] :
    order32TrivialInvariant (H × K) =
      (Nat.card (Subgroup.center H) * Nat.card (Subgroup.center K),
        pow_eq_one_card H 2 * pow_eq_one_card K 2,
        pow_eq_one_card H 4 * pow_eq_one_card K 4,
        sq_image_card H * sq_image_card K) := by
  simp only [order32TrivialInvariant, card_center_prod, pow_eq_one_card_prod, sq_image_card_prod]

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem trivial_invariant_0 :
    order32TrivialInvariant (order32_trivial_reps 0) = (4, 12, 24, 4) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem trivial_invariant_1 :
    order32TrivialInvariant (order32_trivial_reps 1) = (8, 8, 16, 4) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem trivial_invariant_2 :
    order32TrivialInvariant (order32_trivial_reps 2) = (4, 20, 24, 4) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem trivial_invariant_3 :
    order32TrivialInvariant (order32_trivial_reps 3) = (4, 4, 24, 4) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem trivial_invariant_4 :
    order32TrivialInvariant (order32_trivial_reps 4) = (8, 24, 32, 2) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem trivial_invariant_5 :
    order32TrivialInvariant (order32_trivial_reps 5) = (8, 16, 32, 3) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem trivial_invariant_6 :
    order32TrivialInvariant (order32_trivial_reps 6) = (8, 16, 32, 2) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem trivial_invariant_7 :
    order32TrivialInvariant (order32_trivial_reps 7) = (8, 8, 32, 2) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem trivial_invariant_8 :
    order32TrivialInvariant (order32_trivial_reps 8) = (8, 8, 32, 3) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private def order32_trivial_invariant_table : Fin 9 → ℕ × ℕ × ℕ × ℕ
  | 0 => (4, 12, 24, 4)   -- G2 × C2
  | 1 => (8, 8, 16, 4)    -- G3 × C2
  | 2 => (4, 20, 24, 4)   -- G4 × C2
  | 3 => (4, 4, 24, 4)    -- G5 × C2
  | 4 => (8, 24, 32, 2)   -- G8 × C2
  | 5 => (8, 16, 32, 3)   -- G9 × C2
  | 6 => (8, 16, 32, 2)   -- G10 × C2
  | 7 => (8, 8, 32, 2)    -- G11 × C2
  | 8 => (8, 8, 32, 3)    -- G12 × C2

private theorem order32_trivial_invariant_spec (i : Fin 9) :
    order32TrivialInvariant (order32_trivial_reps i) = order32_trivial_invariant_table i := by
  fin_cases i
  exacts [trivial_invariant_0, trivial_invariant_1, trivial_invariant_2, trivial_invariant_3,
    trivial_invariant_4, trivial_invariant_5, trivial_invariant_6, trivial_invariant_7,
    trivial_invariant_8]

theorem order32_trivial_reps_pairwise : PairwiseNonMulEquiv order32_trivial_reps := by
  apply PairwiseNonMulEquiv.of_invariant order32_trivial_invariant_table
  · intro i j ⟨e⟩
    rw [← order32_trivial_invariant_spec i, ← order32_trivial_invariant_spec j]
    exact order32TrivialInvariant_eq_of_mulEquiv e
  · intro i j hij _
    have hinj : Function.Injective order32_trivial_invariant_table := by decide
    exact hinj hij

/-! ### Hidden duplicates among the "new" representatives

`order32_c8c2tw_u3` (`(C₈×C₂) ⋊[ψ₃] C₂`, `G2`'s twisted branch) and `order32_c8c2tw_u7`
(`(C₈×C₂) ⋊[ψ₇] C₂`, `G4`'s twisted branch) are isomorphic, NOT just tied on the
`(center, pow2, pow4, sq_image)` invariant tuple: the automorphism `(x,y) ↦ (x+4y, y)` of
`C₈×C₂` (send the generator `a ↦ a`, `c ↦ a⁴c`) conjugates the twist-by-`3` action into
the twist-by-`7` action, so `semidirectProductCongrConj` directly builds the equivalence.

The SAME conjugating automorphism also connects `order32_c8c2tw_u5` (`G3`'s twist-by-`5`
branch) to `order32_k8xdbl_psi5` (`G9`'s `x`-doubled branch, whose action is exactly the
"twist-by-`1`" case in this family): the pair `(u,u')=(5,1)` satisfies the same conjugating
condition as `(u,u')=(3,7)`, since `5-1 ≡ 3-7 ≡ 4 (mod 8)`. So these two are ALSO
isomorphic, not merely tied.

(By contrast, `(u,u')=(3,5)` or `(5,7)` do NOT satisfy this condition — `3-5≡5-7≡-2 (mod
8)`, and no odd `t` solves `t·(-2) ≡ 0` or `4 (mod 8)` — so no further collapse within the
twisted family beyond these two merges.) -/

/-- The automorphism `(x,y) ↦ (x+4y,y)` of `C₈×C₂` conjugating the `u=3` twist action into
the `u=7` twist action. -/
private noncomputable def swapC8C2_3to7 :
    Multiplicative (ZMod 8) × Multiplicative (ZMod 2) ≃*
      Multiplicative (ZMod 8) × Multiplicative (ZMod 2) where
  toFun p := (Multiplicative.ofAdd (Multiplicative.toAdd p.1
        + 4 * ((Multiplicative.toAdd p.2).val : ZMod 8)), p.2)
  invFun p := (Multiplicative.ofAdd (Multiplicative.toAdd p.1
        + 4 * ((Multiplicative.toAdd p.2).val : ZMod 8)), p.2)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem c8c2tw_phi3_conj_eq_phi7 :
    (MulAut.conj swapC8C2_3to7).toMonoidHom.comp c8c2tw_phi3 = c8c2tw_phi7 := by
  apply MonoidHom.ext
  intro t
  apply MulEquiv.ext
  intro p
  revert t p
  decide

theorem order32_c8c2tw_u3_equiv_u7 :
    Nonempty (order32_c8c2tw_u3 ≃* order32_c8c2tw_u7) :=
  ⟨(semidirectProductCongrConj swapC8C2_3to7).trans
    (semidirectProductCongr_eq c8c2tw_phi3_conj_eq_phi7)⟩

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem c8c2tw_phi5_conj_eq_k8xdbl_psi5 :
    (MulAut.conj swapC8C2_3to7).toMonoidHom.comp c8c2tw_phi5 = c8c2K8y_psi5 := by
  apply MonoidHom.ext
  intro t
  apply MulEquiv.ext
  intro p
  revert t p
  decide

theorem order32_c8c2tw_u5_equiv_k8xdbl_psi5 :
    Nonempty (order32_c8c2tw_u5 ≃* order32_k8xdbl_psi5) :=
  ⟨(semidirectProductCongrConj swapC8C2_3to7).trans
    (semidirectProductCongr_eq c8c2tw_phi5_conj_eq_k8xdbl_psi5)⟩

/-- The 13 genuinely new order-32-specific non-abelian representatives (after dropping
`order32_c8c2tw_u7` and `order32_k8xdbl_psi5`, isomorphic to `order32_c8c2tw_u3` and
`order32_c8c2tw_u5` respectively — see `order32_c8c2tw_u3_equiv_u7` and
`order32_c8c2tw_u5_equiv_k8xdbl_psi5` above). -/
noncomputable abbrev order32_new_reps : Fin 13 → Type
  | 0 => order32_c8c4_u3
  | 1 => order32_c8c2tw_u3
  | 2 => order32_c8c4_u5
  | 3 => order32_c8c2tw_u5
  | 4 => order32_c8c4_u7
  | 5 => order32_c16c2_u7
  | 6 => order32_c16c2_u15
  | 7 => order32_k8c4_psi3
  | 8 => order32_k8xdbl_psi3
  | 9 => order32_k8ydbl_psi3
  | 10 => order32_k8c4_psi5
  | 11 => order32_k8c4_psi6
  | 12 => order32_k8ydbl_psi6

noncomputable instance instGroupOrder32NewReps : ∀ i, Group (order32_new_reps i)
  | 0 => inferInstanceAs (Group order32_c8c4_u3)
  | 1 => inferInstanceAs (Group order32_c8c2tw_u3)
  | 2 => inferInstanceAs (Group order32_c8c4_u5)
  | 3 => inferInstanceAs (Group order32_c8c2tw_u5)
  | 4 => inferInstanceAs (Group order32_c8c4_u7)
  | 5 => inferInstanceAs (Group order32_c16c2_u7)
  | 6 => inferInstanceAs (Group order32_c16c2_u15)
  | 7 => inferInstanceAs (Group order32_k8c4_psi3)
  | 8 => inferInstanceAs (Group order32_k8xdbl_psi3)
  | 9 => inferInstanceAs (Group order32_k8ydbl_psi3)
  | 10 => inferInstanceAs (Group order32_k8c4_psi5)
  | 11 => inferInstanceAs (Group order32_k8c4_psi6)
  | 12 => inferInstanceAs (Group order32_k8ydbl_psi6)

theorem card_order32_new_reps (i : Fin 13) : Nat.card (order32_new_reps i) = 32 := by
  fin_cases i <;>
    first
      | exact card_order32_c8c4_u3
      | exact card_order32_c8c2tw_u3
      | exact card_order32_c8c4_u5
      | exact card_order32_c8c2tw_u5
      | exact card_order32_c8c4_u7
      | exact card_order32_c16c2_u7
      | exact card_order32_c16c2_u15
      | exact card_order32_k8c4_psi3
      | exact card_order32_k8xdbl_psi3
      | exact card_order32_k8ydbl_psi3
      | exact card_order32_k8c4_psi5
      | exact card_order32_k8c4_psi6
      | exact card_order32_k8ydbl_psi6

/-! ### Initial coarse-invariant pass on 9 of the 13 genuinely-new representatives

At this stage two ties remain unresolved among the 13 genuinely-new representatives,
both tied on
the `(|Z(·)|, pow_eq_one_card _ 2, _ 4, sq_image_card _)` tuple:

* `order32_k8c4_psi5` vs `order32_k8c4_psi6` — both `(8, 8, 32, 4)`.
* `order32_k8ydbl_psi3` vs `order32_k8ydbl_psi6` — both `(8, 12, 32, 4)`.

Unlike the two merges above, the `psi5`/`psi6` pair can NOT be resolved by a conjugating
automorphism of their shared normal factor `K₈`: any such automorphism would force
`order16_wild_G9 ≃* order16_wild_G10` (via the identical construction, with `H = C₂`
instead of `C₄`), contradicting their already-proven distinctness
(`order16_wild_pairwise_noniso`). So this pair is either separated by a strictly finer
invariant (e.g. `Nat.card (frattini ·)`, untested) or requires some other argument.
The `k8ydbl_psi3`/`psi6` pair's status is unknown.  The first pair is resolved later in
this file by a powered-commuting-pair count; the second remains open.

This section proves distinctness only for the remaining 9 representatives (indices `0`–`8`
of `order32_new_reps`), via the same 4-tuple invariant. -/

/-- The 9 genuinely-new representatives NOT involved in either open tie. -/
noncomputable abbrev order32_new_reps_resolved : Fin 9 → Type
  | 0 => order32_c8c4_u3
  | 1 => order32_c8c2tw_u3
  | 2 => order32_c8c4_u5
  | 3 => order32_c8c2tw_u5
  | 4 => order32_c8c4_u7
  | 5 => order32_c16c2_u7
  | 6 => order32_c16c2_u15
  | 7 => order32_k8c4_psi3
  | 8 => order32_k8xdbl_psi3

noncomputable instance instGroupOrder32NewRepsResolved : ∀ i, Group (order32_new_reps_resolved i)
  | 0 => inferInstanceAs (Group order32_c8c4_u3)
  | 1 => inferInstanceAs (Group order32_c8c2tw_u3)
  | 2 => inferInstanceAs (Group order32_c8c4_u5)
  | 3 => inferInstanceAs (Group order32_c8c2tw_u5)
  | 4 => inferInstanceAs (Group order32_c8c4_u7)
  | 5 => inferInstanceAs (Group order32_c16c2_u7)
  | 6 => inferInstanceAs (Group order32_c16c2_u15)
  | 7 => inferInstanceAs (Group order32_k8c4_psi3)
  | 8 => inferInstanceAs (Group order32_k8xdbl_psi3)

theorem card_order32_new_reps_resolved (i : Fin 9) :
    Nat.card (order32_new_reps_resolved i) = 32 := by
  fin_cases i <;>
    first
      | exact card_order32_c8c4_u3
      | exact card_order32_c8c2tw_u3
      | exact card_order32_c8c4_u5
      | exact card_order32_c8c2tw_u5
      | exact card_order32_c8c4_u7
      | exact card_order32_c16c2_u7
      | exact card_order32_c16c2_u15
      | exact card_order32_k8c4_psi3
      | exact card_order32_k8xdbl_psi3

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem new_invariant_0 :
    order32TrivialInvariant (order32_new_reps_resolved 0) = (4, 4, 24, 6) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem new_invariant_1 :
    order32TrivialInvariant (order32_new_reps_resolved 1) = (4, 12, 24, 5) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem new_invariant_2 :
    order32TrivialInvariant (order32_new_reps_resolved 2) = (8, 4, 16, 8) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem new_invariant_3 :
    order32TrivialInvariant (order32_new_reps_resolved 3) = (8, 8, 16, 6) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem new_invariant_4 :
    order32TrivialInvariant (order32_new_reps_resolved 4) = (4, 4, 24, 5) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem new_invariant_5 :
    order32TrivialInvariant (order32_new_reps_resolved 5) = (2, 10, 20, 8) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem new_invariant_6 :
    order32TrivialInvariant (order32_new_reps_resolved 6) = (2, 18, 20, 8) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem new_invariant_7 :
    order32TrivialInvariant (order32_new_reps_resolved 7) = (8, 8, 32, 3) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- large finite decide over concrete order-32 group elements
private theorem new_invariant_8 :
    order32TrivialInvariant (order32_new_reps_resolved 8) = (4, 20, 24, 4) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private def order32_new_invariant_table : Fin 9 → ℕ × ℕ × ℕ × ℕ
  | 0 => (4, 4, 24, 6)
  | 1 => (4, 12, 24, 5)
  | 2 => (8, 4, 16, 8)
  | 3 => (8, 8, 16, 6)
  | 4 => (4, 4, 24, 5)
  | 5 => (2, 10, 20, 8)
  | 6 => (2, 18, 20, 8)
  | 7 => (8, 8, 32, 3)
  | 8 => (4, 20, 24, 4)

private theorem order32_new_invariant_spec (i : Fin 9) :
    order32TrivialInvariant (order32_new_reps_resolved i) = order32_new_invariant_table i := by
  fin_cases i
  exacts [new_invariant_0, new_invariant_1, new_invariant_2, new_invariant_3, new_invariant_4,
    new_invariant_5, new_invariant_6, new_invariant_7, new_invariant_8]

theorem order32_new_reps_resolved_pairwise : PairwiseNonMulEquiv order32_new_reps_resolved := by
  apply PairwiseNonMulEquiv.of_invariant order32_new_invariant_table
  · intro i j ⟨e⟩
    rw [← order32_new_invariant_spec i, ← order32_new_invariant_spec j]
    exact order32TrivialInvariant_eq_of_mulEquiv e
  · intro i j hij _
    have hinj : Function.Injective order32_new_invariant_table := by decide
    exact hinj hij

/-! ### Resolving the `k8c4_psi5` / `k8c4_psi6` tie

The old four-coordinate invariant gives `(8, 8, 32, 4)` for both groups.  Counting
ordered commuting pairs with the first element of exponent dividing `m` and the second
of exponent dividing `n` is a finer isomorphism invariant.  At `(m,n)=(2,4)` the two
values are `256` and `192`. -/

noncomputable def order32PoweredCommutingPairCard (H : Type*) [Group H]
    (m n : ℕ) : ℕ :=
  Nat.card {p : H × H //
    p.1 * p.2 = p.2 * p.1 ∧ p.1 ^ m = 1 ∧ p.2 ^ n = 1}

noncomputable def order32PoweredCommutingPairEquivOfMulEquiv
    {H K : Type*} [Group H] [Group K] (m n : ℕ) (e : H ≃* K) :
    {p : H × H // p.1 * p.2 = p.2 * p.1 ∧ p.1 ^ m = 1 ∧ p.2 ^ n = 1} ≃
      {p : K × K // p.1 * p.2 = p.2 * p.1 ∧ p.1 ^ m = 1 ∧ p.2 ^ n = 1} where
  toFun p := ⟨(e p.1.1, e p.1.2), by
    refine ⟨?_, ?_, ?_⟩
    · simpa [map_mul] using congrArg e p.2.1
    · rw [← map_pow, p.2.2.1, map_one]
    · rw [← map_pow, p.2.2.2, map_one]⟩
  invFun p := ⟨(e.symm p.1.1, e.symm p.1.2), by
    refine ⟨?_, ?_, ?_⟩
    · simpa [map_mul] using congrArg e.symm p.2.1
    · rw [← map_pow]
      exact e.injective (by simp [p.2.2.1])
    · rw [← map_pow]
      exact e.injective (by simp [p.2.2.2])⟩
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

theorem order32PoweredCommutingPairCard_eq_of_mulEquiv
    {H K : Type*} [Group H] [Group K] (m n : ℕ) (e : H ≃* K) :
    order32PoweredCommutingPairCard H m n = order32PoweredCommutingPairCard K m n :=
  Nat.card_congr (order32PoweredCommutingPairEquivOfMulEquiv m n e)

set_option maxHeartbeats 4000000 in -- finite count over 32² concrete pairs
private theorem powered_commuting_pair_psi5 :
    order32PoweredCommutingPairCard order32_k8c4_psi5 2 4 = 256 := by
  rw [order32PoweredCommutingPairCard, Nat.card_eq_fintype_card]
  decide +kernel

set_option maxHeartbeats 4000000 in -- finite count over 32² concrete pairs
private theorem powered_commuting_pair_psi6 :
    order32PoweredCommutingPairCard order32_k8c4_psi6 2 4 = 192 := by
  rw [order32PoweredCommutingPairCard, Nat.card_eq_fintype_card]
  decide +kernel

theorem order32_k8c4_psi5_not_equiv_psi6 :
    ¬ Nonempty (order32_k8c4_psi5 ≃* order32_k8c4_psi6) := by
  rintro ⟨e⟩
  have h := order32PoweredCommutingPairCard_eq_of_mulEquiv 2 4 e
  rw [powered_commuting_pair_psi5, powered_commuting_pair_psi6] at h
  omega

/-- The newly separated pair, packaged as a two-element family. -/
noncomputable abbrev order32_k8c4_tied_reps : Fin 2 → Type
  | 0 => order32_k8c4_psi5
  | 1 => order32_k8c4_psi6

noncomputable instance instGroupOrder32K8C4TiedReps :
    ∀ i, Group (order32_k8c4_tied_reps i)
  | 0 => inferInstanceAs (Group order32_k8c4_psi5)
  | 1 => inferInstanceAs (Group order32_k8c4_psi6)

theorem card_order32_k8c4_tied_reps (i : Fin 2) :
    Nat.card (order32_k8c4_tied_reps i) = 32 := by
  fin_cases i
  · exact card_order32_k8c4_psi5
  · exact card_order32_k8c4_psi6

set_option maxHeartbeats 4000000 in -- finite invariants over concrete order-32 elements
private theorem old_invariant_psi5 :
    order32TrivialInvariant order32_k8c4_psi5 = (8, 8, 32, 4) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in -- finite invariants over concrete order-32 elements
private theorem old_invariant_psi6 :
    order32TrivialInvariant order32_k8c4_psi6 = (8, 8, 32, 4) :=
  order32TrivialInvariant_eq_of_counts (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private theorem order32_k8c4_tied_invariant_spec (i : Fin 2) :
    order32TrivialInvariant (order32_k8c4_tied_reps i) = (8, 8, 32, 4) := by
  fin_cases i
  · exact old_invariant_psi5
  · exact old_invariant_psi6

theorem order32_k8c4_tied_reps_pairwise :
    PairwiseNonMulEquiv order32_k8c4_tied_reps := by
  rintro i j ⟨e⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd ⟨e⟩ order32_k8c4_psi5_not_equiv_psi6
  · exact absurd ⟨e.symm⟩ order32_k8c4_psi5_not_equiv_psi6
  · rfl

theorem order32_resolved_disjoint_k8c4_tied (i : Fin 9) (j : Fin 2) :
    ¬ Nonempty (order32_new_reps_resolved i ≃* order32_k8c4_tied_reps j) := by
  rintro ⟨e⟩
  have h := order32TrivialInvariant_eq_of_mulEquiv e
  rw [order32_new_invariant_spec i, order32_k8c4_tied_invariant_spec j] at h
  revert h
  fin_cases i <;> decide

theorem order32_trivial_disjoint_k8c4_tied (i : Fin 9) (j : Fin 2) :
    ¬ Nonempty (order32_trivial_reps i ≃* order32_k8c4_tied_reps j) := by
  rintro ⟨e⟩
  have h := order32TrivialInvariant_eq_of_mulEquiv e
  rw [order32_trivial_invariant_spec i, order32_k8c4_tied_invariant_spec j] at h
  revert h
  fin_cases i <;> decide

/-! ### Final assembly

Two of the 9 "resolved" new representatives (`order32_k8c4_psi3`, index `7`, and
`order32_k8xdbl_psi3`, index `8`) turn out to be tied on `order32TrivialInvariant` with two
of the `Qᵢ × C₂` representatives (`order16_wild_G12 × C₂` and `order16_wild_G4 × C₂`
respectively): `(8,8,32,3)` and `(4,20,24,4)`. As with the two intra-family ties above,
whether these are genuine isomorphisms or just an insufficiently sharp invariant is left
open — this is NOT investigated further here (per the "park the rest" decision), so the
final assembled result also excludes these 2 representatives, using only the 7 that are
fully cross-checked disjoint from every other family. -/

/-- The 7 genuinely-new representatives free of ALL currently-known ties (intra- and
cross-family). -/
noncomputable abbrev order32_new_reps_final : Fin 7 → Type
  | 0 => order32_c8c4_u3
  | 1 => order32_c8c2tw_u3
  | 2 => order32_c8c4_u5
  | 3 => order32_c8c2tw_u5
  | 4 => order32_c8c4_u7
  | 5 => order32_c16c2_u7
  | 6 => order32_c16c2_u15

noncomputable instance instGroupOrder32NewRepsFinal : ∀ i, Group (order32_new_reps_final i)
  | 0 => inferInstanceAs (Group order32_c8c4_u3)
  | 1 => inferInstanceAs (Group order32_c8c2tw_u3)
  | 2 => inferInstanceAs (Group order32_c8c4_u5)
  | 3 => inferInstanceAs (Group order32_c8c2tw_u5)
  | 4 => inferInstanceAs (Group order32_c8c4_u7)
  | 5 => inferInstanceAs (Group order32_c16c2_u7)
  | 6 => inferInstanceAs (Group order32_c16c2_u15)

theorem card_order32_new_reps_final (i : Fin 7) : Nat.card (order32_new_reps_final i) = 32 := by
  fin_cases i <;>
    first
      | exact card_order32_c8c4_u3
      | exact card_order32_c8c2tw_u3
      | exact card_order32_c8c4_u5
      | exact card_order32_c8c2tw_u5
      | exact card_order32_c8c4_u7
      | exact card_order32_c16c2_u7
      | exact card_order32_c16c2_u15

private def order32_new_final_invariant_table : Fin 7 → ℕ × ℕ × ℕ × ℕ
  | 0 => (4, 4, 24, 6)
  | 1 => (4, 12, 24, 5)
  | 2 => (8, 4, 16, 8)
  | 3 => (8, 8, 16, 6)
  | 4 => (4, 4, 24, 5)
  | 5 => (2, 10, 20, 8)
  | 6 => (2, 18, 20, 8)

private theorem order32_new_final_invariant_spec (i : Fin 7) :
    order32TrivialInvariant (order32_new_reps_final i) = order32_new_final_invariant_table i := by
  fin_cases i
  exacts [new_invariant_0, new_invariant_1, new_invariant_2, new_invariant_3, new_invariant_4,
    new_invariant_5, new_invariant_6]

theorem order32_new_reps_final_pairwise : PairwiseNonMulEquiv order32_new_reps_final := by
  apply PairwiseNonMulEquiv.of_invariant order32_new_final_invariant_table
  · intro i j ⟨e⟩
    rw [← order32_new_final_invariant_spec i, ← order32_new_final_invariant_spec j]
    exact order32TrivialInvariant_eq_of_mulEquiv e
  · intro i j hij _
    have hinj : Function.Injective order32_new_final_invariant_table := by decide
    exact hinj hij

/-- Cross-family disjointness of the 9 `Qᵢ × C₂` reps and the 7 final new reps: their
`order32TrivialInvariant` tuples are all pairwise distinct (checked directly). -/
theorem order32_trivial_disjoint_new_final (i : Fin 9) (j : Fin 7) :
    ¬ Nonempty (order32_trivial_reps i ≃* order32_new_reps_final j) := by
  rintro ⟨e⟩
  have h := order32TrivialInvariant_eq_of_mulEquiv e
  rw [order32_trivial_invariant_spec i, order32_new_final_invariant_spec j] at h
  revert h; fin_cases i <;> fin_cases j <;> decide

/-- Every `Qᵢ × C₂` representative has center of size `≤ 8`. -/
theorem order32_trivial_center_le (i : Fin 9) :
    Nat.card (Subgroup.center (order32_trivial_reps i)) ≤ 8 := by
  have h : Nat.card (Subgroup.center (order32_trivial_reps i))
      = (order32_trivial_invariant_table i).1 :=
    congrArg Prod.fst (order32_trivial_invariant_spec i)
  rw [h]; fin_cases i <;> decide

/-- Every final-new representative has center of size `≤ 8`. -/
theorem order32_new_final_center_le (i : Fin 7) :
    Nat.card (Subgroup.center (order32_new_reps_final i)) ≤ 8 := by
  have h : Nat.card (Subgroup.center (order32_new_reps_final i))
      = (order32_new_final_invariant_table i).1 :=
    congrArg Prod.fst (order32_new_final_invariant_spec i)
  rw [h]; fin_cases i <;> decide

/-- Every abelian representative has center equal to the whole group (`32`), since abelian
groups are their own center. -/
theorem order32_abelian_center_eq (i : Fin 7) :
    Nat.card (Subgroup.center (order32_abelian_reps i)) = 32 := by
  have hcomm : ∀ a b : order32_abelian_reps i, a * b = b * a := by
    fin_cases i <;> intro a b <;> exact mul_comm a b
  letI : CommGroup (order32_abelian_reps i) :=
    { (inferInstance : Group (order32_abelian_reps i)) with mul_comm := hcomm }
  rw [Subgroup.center_eq_top]
  simpa using card_order32_abelian_reps i

/-- The `Qᵢ × C₂` and final-new representatives, combined into a single non-abelian
family (`Fin 9 ⊕ Fin 7`), pairwise non-isomorphic. -/
theorem order32_nonabelian_reps_pairwise :
    PairwiseNonMulEquiv (Sum.elim order32_trivial_reps order32_new_reps_final) :=
  order32_trivial_reps_pairwise.sum order32_new_reps_final_pairwise
    order32_trivial_disjoint_new_final

/-- **Partial result**: 23 of the concrete order-32 representatives constructed so far
(the 7 abelian types, the 9 `Qᵢ × C₂` types, and 7 of the 13 genuinely-new types) are
pairwise non-isomorphic. This legacy subfamily excludes 6 representatives that the
coarse invariant did not separate (documented above and in the module doc): the
`c8c2tw_u7`/`k8xdbl_psi5` duplicates were already merged away, but `k8c4_psi5` vs
`k8c4_psi6`, `k8ydbl_psi3` vs `k8ydbl_psi6`, and the two new/trivial cross-ties
(`k8c4_psi3` vs `G12×C2`, `k8xdbl_psi3` vs `G4×C2`) were unresolved at this stage.
The stronger theorem below recovers the `k8c4_psi5`/`psi6` pair. -/
theorem order32_partial_distinct :
    PairwiseNonMulEquiv
      (Sum.elim order32_abelian_reps (Sum.elim order32_trivial_reps order32_new_reps_final)) :=
  order32_abelian_reps_pairwise.sum order32_nonabelian_reps_pairwise
    (fun i j hiso => by
      obtain ⟨e⟩ := hiso
      have h1 := order32_abelian_center_eq i
      rcases j with j | j
      · have e' : order32_abelian_reps i ≃* order32_trivial_reps j := e
        have h3 := card_center_eq_of_mulEquiv e'
        have h2 := order32_trivial_center_le j
        omega
      · have e' : order32_abelian_reps i ≃* order32_new_reps_final j := e
        have h3 := card_center_eq_of_mulEquiv e'
        have h2 := order32_new_final_center_le j
        omega)

/-! ### Strengthened 25-representative result

The powered-commuting-pair invariant above lets us add both `k8c4_psi5` and
`k8c4_psi6` to the previously assembled 23 representatives. -/

theorem order32_new_final_disjoint_k8c4_tied (i : Fin 7) (j : Fin 2) :
    ¬ Nonempty (order32_new_reps_final i ≃* order32_k8c4_tied_reps j) := by
  rintro ⟨e⟩
  have h := order32TrivialInvariant_eq_of_mulEquiv e
  rw [order32_new_final_invariant_spec i, order32_k8c4_tied_invariant_spec j] at h
  revert h
  fin_cases i <;> decide

theorem order32_k8c4_tied_center_eq (i : Fin 2) :
    Nat.card (Subgroup.center (order32_k8c4_tied_reps i)) = 8 := by
  exact congrArg Prod.fst (order32_k8c4_tied_invariant_spec i)

theorem order32_abelian_disjoint_k8c4_tied (i : Fin 7) (j : Fin 2) :
    ¬ Nonempty (order32_abelian_reps i ≃* order32_k8c4_tied_reps j) := by
  rintro ⟨e⟩
  have h := card_center_eq_of_mulEquiv e
  rw [order32_abelian_center_eq i, order32_k8c4_tied_center_eq j] at h
  omega

/-- **Improved partial result**: 25 concrete groups of order 32 are pairwise
non-isomorphic.  Compared with `order32_partial_distinct`, this adds the two groups
separated by the powered-commuting-pair count. -/
theorem order32_partial_distinct_25 :
    PairwiseNonMulEquiv
      (Sum.elim
        (Sum.elim order32_abelian_reps
          (Sum.elim order32_trivial_reps order32_new_reps_final))
        order32_k8c4_tied_reps) :=
  order32_partial_distinct.sum order32_k8c4_tied_reps_pairwise
    (fun i j => by
      rcases i with i | i
      · exact order32_abelian_disjoint_k8c4_tied i j
      · rcases i with i | i
        · exact order32_trivial_disjoint_k8c4_tied i j
        · exact order32_new_final_disjoint_k8c4_tied i j)

end Smallgroups.UsefulTheorems
