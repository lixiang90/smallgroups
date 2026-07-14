/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.P3Group
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Smallgroups.UsefulTheorems.SemidirectProductClassify
import Smallgroups.UsefulTheorems.Order72.Sylow
import Mathlib.Data.ZMod.Aut
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.GroupTheory.PGroup

/-!
# Groups of order 72: the Sylow-2-normal branch (`H ⋊ P`, `H` order `8`, `P` order `9`)

If `G` has order `72` and its Sylow-`2` subgroup `H` (order `8`) is normal, Schur–Zassenhaus
gives `G ≃* H ⋊[φ] P` for `P` a complement of order `9`. `H` is one of the five order-`8`
types (`P3Group`), and `P` is one of the two order-`9` types (`prime_sq_classification`).

Since `|P| = 9 = 3²`, the action `φ : P →* MulAut H` always has image a finite `3`-group.
For three of the five `H`-types, `Nat.card (MulAut H)` is coprime to `3`, forcing `φ` to be
**trivial** regardless of which of the two `P`-types is used — so those combinations only
contribute the direct product `H × P`:

* `H = CyclicP3 2 ≃ ZMod 8`: `Nat.card (MulAut H) = φ(8) = 4` (via `ZMod.AddAutEquivUnits`
  and `MulAutMultiplicative`).
* `H = AbelianP2P 2 ≃ ZMod 4 × ZMod 2`, `H = DihedralGroup 4`: `Nat.card (MulAut H) = 8`.

The remaining two `H`-types, `QuaternionGroup 2` (`Aut ≅ S₄`, order `24`) and
`ElementaryP3 2 ≃ (ZMod 2)³` (`Aut ≅ GL(3,2)`, order `168`), genuinely admit order-`3`
automorphisms and need dedicated (not-yet-built) case analysis — tracked separately.

For `AbelianP2P 2` and `DihedralGroup 4`, `Nat.card (MulAut H)` isn't cheaply computable
(no totient-style formula, and brute-force search over `Equiv.Perm H` is too expensive), so
instead we directly prove "no automorphism of order `3`" by tracking a single generator's
orbit through `f` via `f³ = 1` (see `card_mulAut_abelianP2P_two_no_order_three` and
`card_mulAut_dihedralGroup_four_no_order_three`) — no permutation search involved.
-/

namespace Smallgroups.UsefulTheorems

open P3Group

/-! ### A general helper: a hom from a group of order `9` into an `Aut` group whose order is
coprime to `3` is trivial. -/

theorem mulAut_hom_trivial_of_not_three_dvd {H K : Type*} [Group H] [Group K] [Finite K]
    [Finite (MulAut H)] (hK : Nat.card K = 9)
    (hcop : ¬ (3 : ℕ) ∣ Nat.card (MulAut H)) (φ : K →* MulAut H) (k : K) : φ k = 1 := by
  have hordK : orderOf k ∣ 9 := hK ▸ orderOf_dvd_natCard k
  have hdvd1 : orderOf (φ k) ∣ orderOf k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
  have hdvd9 : orderOf (φ k) ∣ 9 := hdvd1.trans hordK
  have hdvdA : orderOf (φ k) ∣ Nat.card (MulAut H) := orderOf_dvd_natCard _
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9] at hdvd9
  obtain ⟨j, hj2, hje⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd9
  interval_cases j
  · rw [pow_zero] at hje; exact orderOf_eq_one_iff.mp hje
  · exfalso; apply hcop
    rw [pow_one] at hje
    exact hje ▸ hdvdA
  · exfalso; apply hcop
    have h3d9 : (3 : ℕ) ∣ 3 ^ 2 := ⟨3, by norm_num⟩
    exact (hje ▸ h3d9).trans hdvdA

/-! ### `Nat.card (MulAut H)` for the "easy" `H`-types. -/

/-- `Aut(ℤ/n)` has order `φ(n)` (Euler's totient). -/
theorem card_mulAut_multiplicative_zmod (n : ℕ) [NeZero n] :
    Nat.card (MulAut (Multiplicative (ZMod n))) = n.totient := by
  have h1 : Nat.card (MulAut (Multiplicative (ZMod n))) = Nat.card (AddAut (ZMod n)) :=
    Nat.card_congr (MulAutMultiplicative (G := ZMod n)).toEquiv
  have h2 : Nat.card (AddAut (ZMod n)) = Nat.card (ZMod n)ˣ :=
    Nat.card_congr (ZMod.AddAutEquivUnits n).toEquiv
  rw [h1, h2, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

theorem card_mulAut_cyclicP3_two : Nat.card (MulAut (Multiplicative (ZMod 8))) = 4 := by
  rw [card_mulAut_multiplicative_zmod]; decide

/-! ### A second helper: trivial action from "no order-`3` automorphism" directly (avoids
needing `Nat.card (MulAut H)` at all — useful when that cardinality isn't cheaply
computable). -/

theorem mulAut_hom_trivial_of_no_order_three {H K : Type*} [Group H] [Group K] [Finite K]
    (hK : Nat.card K = 9) (hno3 : ∀ f : MulAut H, f ^ 3 = 1 → f = 1)
    (φ : K →* MulAut H) (k : K) : φ k = 1 := by
  have hordK : orderOf k ∣ 9 := hK ▸ orderOf_dvd_natCard k
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9] at hordK
  obtain ⟨j, hj2, hje⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hordK
  have hk3j : k ^ (3 ^ j) = 1 := hje ▸ pow_orderOf_eq_one k
  have hφ : (φ k) ^ (3 ^ j) = 1 := by rw [← map_pow, hk3j, map_one]
  interval_cases j
  · simpa using hφ
  · exact hno3 (φ k) (by simpa using hφ)
  · have h1 : (φ k) ^ 3 = 1 :=
      hno3 ((φ k) ^ 3) (by rw [← pow_mul]; norm_num at hφ ⊢; exact hφ)
    exact hno3 (φ k) h1

/-! ### `AbelianP2P 2 ≃ ℤ/4 × ℤ/2` has no order-`3` automorphism.

Proof sketch (no brute-force search over `Equiv.Perm H`): write `e1 = (1,0)`, `e2 = (0,1)`,
`z = e1² = (2,0)`. Every order-`4` element of `H` squares to the same `z`, so `z` is fixed
by any automorphism (`f z = f (e1 ^ 2) = (f e1) ^ 2 = z`, since `f e1` is again an order-`4`
element). Given `f ^ 3 = 1`: tracking the single generator `e2` through `f` directly (no
permutation enumeration) shows `f e2 = e2` (the alternative `f e2 = e2 * z` immediately
contradicts `f ^ 3 = 1` via a 2-line computation). A parallel argument on `e1` (using
`f e2 = e2` already established) then forces `f e1 = e1`, and since `e1, e2` generate `H`,
`f = 1`. -/

abbrev H2 := Multiplicative (ZMod 4) × Multiplicative (ZMod 2)

private def h2e1 : H2 := (Multiplicative.ofAdd (1 : ZMod 4), 1)
private def h2e2 : H2 := (1, Multiplicative.ofAdd (1 : ZMod 2))
private def h2z : H2 := (Multiplicative.ofAdd (2 : ZMod 4), 1)

private theorem h2e1sq : h2e1 ^ 2 = h2z := by decide
private theorem h2e1pow4 : h2e1 ^ 4 = 1 := by decide
private theorem h2e1sq_ne1 : h2e1 ^ 2 ≠ 1 := by decide
private theorem h2zsq : h2z ^ 2 = 1 := by decide
private theorem h2e2sq : h2e2 ^ 2 = 1 := by decide
private theorem h2zne1 : h2z ≠ 1 := by decide
private theorem h2e2nez : h2e2 ≠ h2z := by decide
private theorem h2e2ne1 : h2e2 ≠ 1 := by decide

private theorem h2sq_eq_z : ∀ x : H2, x ^ 4 = 1 → x ^ 2 ≠ 1 → x ^ 2 = h2z := by decide

private theorem h2order2_mem : ∀ x : H2, x ^ 2 = 1 →
    (x = 1 ∨ x = h2z ∨ x = h2e2 ∨ x = h2e2 * h2z) := by decide

private theorem h2order4_mem : ∀ x : H2, x ^ 4 = 1 → x ^ 2 ≠ 1 →
    (x = h2e1 ∨ x = h2e1⁻¹ ∨ x = h2e1 * h2e2 ∨ x = h2e1⁻¹ * h2e2) := by decide

private theorem h2gen : ∀ x : H2, x = 1 ∨ x = h2e1 ∨ x = h2e1 ^ 2 ∨ x = h2e1 ^ 3 ∨ x = h2e2 ∨
    x = h2e1 * h2e2 ∨ x = h2e1 ^ 2 * h2e2 ∨ x = h2e1 ^ 3 * h2e2 := by decide

theorem card_mulAut_abelianP2P_two_no_order_three :
    ∀ f : MulAut H2, f ^ 3 = 1 → f = 1 := by
  intro f hf3
  have hfapp : ∀ g : H2, (f ^ 3) g = g := by intro g; rw [hf3]; rfl
  have hfe1_4 : (f h2e1) ^ 4 = 1 := by rw [← map_pow, h2e1pow4, map_one]
  have hfe1_sq_ne1 : (f h2e1) ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro hcontra
    exact h2e1sq_ne1 (f.injective (by rw [hcontra, map_one]))
  have hfe1_sq : (f h2e1) ^ 2 = h2z := h2sq_eq_z (f h2e1) hfe1_4 hfe1_sq_ne1
  have hfz : f h2z = h2z := by rw [← h2e1sq, map_pow, hfe1_sq, h2e1sq]
  have hfe2_sq : (f h2e2) ^ 2 = 1 := by rw [← map_pow, h2e2sq, map_one]
  have hfe2_ne1 : f h2e2 ≠ 1 := fun h => h2e2ne1 (f.injective (by rw [h, map_one]))
  have hfe2_nez : f h2e2 ≠ h2z := fun h => h2e2nez (f.injective (h.trans hfz.symm))
  have hfe2_cases : f h2e2 = h2e2 ∨ f h2e2 = h2e2 * h2z := by
    rcases h2order2_mem (f h2e2) hfe2_sq with h | h | h | h
    · exact absurd h hfe2_ne1
    · exact absurd h hfe2_nez
    · exact Or.inl h
    · exact Or.inr h
  have hfe2 : f h2e2 = h2e2 := by
    rcases hfe2_cases with h | h
    · exact h
    · exfalso
      have hf2e2 : f (f h2e2) = h2e2 := by
        rw [h, map_mul, h, hfz, mul_assoc, ← sq, h2zsq, mul_one]
      have h3 : f (f (f h2e2)) = f h2e2 := congrArg f hf2e2
      have h3' : f (f (f h2e2)) = h2e2 := hfapp h2e2
      have hthis : f h2e2 = h2e2 := h3.symm.trans h3'
      rw [h] at hthis
      have heq2 : h2e2 * h2z = h2e2 * 1 := by rw [mul_one]; exact hthis
      exact h2zne1 (mul_left_cancel heq2)
  have hfe1 : f h2e1 = h2e1 := by
    rcases h2order4_mem (f h2e1) hfe1_4 hfe1_sq_ne1 with h | h | h | h
    · exact h
    all_goals {
      exfalso
      have hf3e1 : (f ^ 3) h2e1 = h2e1 := hfapp h2e1
      have heq : f (f (f h2e1)) = h2e1 := hf3e1
      rw [h] at heq
      simp only [map_mul, map_inv, hfe2] at heq
      rw [h] at heq
      simp only [map_mul, map_inv, hfe2] at heq
      rw [h] at heq
      revert heq
      decide
    }
  apply DFunLike.ext
  intro x
  change f x = x
  rcases h2gen x with h | h | h | h | h | h | h | h <;>
    simp [h, map_pow, map_mul, hfe1, hfe2]

/-! ### `DihedralGroup 4` has no order-`3` automorphism.

Same technique as `AbelianP2P 2`, adapted to the (non-abelian) dihedral relations. There
are only **two** order-`4` elements here (`r 1`, `r 3` — reflections all have order `2`),
so `f (r 1)` is pinned directly by the coprimality of `3` and `|Sym(2\text{-set})| = 2` (no
separate "square-to-`z`" detour needed for this half). The order-`2` generator `sr 0` then
has **four** candidate images (the four reflections), ruled down to the fixed choice by
tracking the orbit of `sr 0` through `f` via `f³ = 1`, using left-multiplication bookkeeping
(`d1 ^ k * d2`, not `d2 * d1 ^ k` — the group is non-abelian, unlike the `H2` case above). -/

private def d4d1 : DihedralGroup 4 := DihedralGroup.r 1
private def d4d2 : DihedralGroup 4 := DihedralGroup.sr 0
private def d4z : DihedralGroup 4 := DihedralGroup.r 2

private theorem d4d1sq : d4d1 ^ 2 = d4z := by decide
private theorem d4d1pow3 : d4d1 ^ 3 ≠ 1 := by decide
private theorem d4d1pow4 : d4d1 ^ 4 = 1 := by decide
private theorem d4d1sq_ne1 : d4d1 ^ 2 ≠ 1 := by decide
private theorem d4d1ne1 : d4d1 ≠ 1 := by decide
private theorem d4d1ned1inv : d4d1 ≠ d4d1⁻¹ := by decide
private theorem d4d2sq : d4d2 ^ 2 = 1 := by decide
private theorem d4zne1 : d4z ≠ 1 := by decide
private theorem d4d2nez : d4d2 ≠ d4z := by decide
private theorem d4d2ne1 : d4d2 ≠ 1 := by decide

private theorem d4order4_mem : ∀ x : DihedralGroup 4, x ^ 4 = 1 → x ^ 2 ≠ 1 →
    (x = d4d1 ∨ x = d4d1⁻¹) := by decide

private theorem d4order2_mem : ∀ x : DihedralGroup 4, x ^ 2 = 1 →
    (x = 1 ∨ x = d4z ∨ x = d4d2 ∨ x = d4d1 * d4d2 ∨ x = d4d1 ^ 2 * d4d2 ∨
      x = d4d1 ^ 3 * d4d2) := by decide

private theorem d4gen : ∀ x : DihedralGroup 4, x = 1 ∨ x = d4d1 ∨ x = d4d1 ^ 2 ∨
    x = d4d1 ^ 3 ∨ x = d4d2 ∨ x = d4d1 * d4d2 ∨ x = d4d1 ^ 2 * d4d2 ∨
    x = d4d1 ^ 3 * d4d2 := by decide

private theorem d4calc1 : d4d1 * (d4d1 * d4d2) = d4d1 ^ 2 * d4d2 := by decide
private theorem d4calc2 : d4d1 ^ 2 * (d4d1 * d4d2) = d4d1 ^ 3 * d4d2 := by decide
private theorem d4calc3 : d4d1 ^ 2 * (d4d1 ^ 2 * d4d2) = d4d2 := by decide
private theorem d4calc4 : d4d1 ^ 3 * (d4d1 ^ 3 * d4d2) = d4d1 ^ 2 * d4d2 := by decide
private theorem d4calc5 : d4d1 ^ 2 * (d4d1 ^ 3 * d4d2) = d4d1 * d4d2 := by decide

theorem card_mulAut_dihedralGroup_four_no_order_three :
    ∀ f : MulAut (DihedralGroup 4), f ^ 3 = 1 → f = 1 := by
  intro f hf3
  have hfapp : ∀ g : DihedralGroup 4, (f ^ 3) g = g := by intro g; rw [hf3]; rfl
  have hfe1_4 : (f d4d1) ^ 4 = 1 := by rw [← map_pow, d4d1pow4, map_one]
  have hfe1_sq_ne1 : (f d4d1) ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro hcontra
    exact d4d1sq_ne1 (f.injective (by rw [hcontra, map_one]))
  have hfe1 : f d4d1 = d4d1 := by
    rcases d4order4_mem (f d4d1) hfe1_4 hfe1_sq_ne1 with h | h
    · exact h
    · exfalso
      have hf2 : f (f d4d1) = d4d1 := by rw [h, map_inv, h, inv_inv]
      have h3 : f (f (f d4d1)) = f d4d1 := congrArg f hf2
      have h3' : f (f (f d4d1)) = d4d1 := hfapp d4d1
      have heq : f d4d1 = d4d1 := h3.symm.trans h3'
      rw [h] at heq
      exact d4d1ned1inv heq.symm
  have hfz : f d4z = d4z := by rw [← d4d1sq, map_pow, hfe1]
  have hfe2_sq : (f d4d2) ^ 2 = 1 := by rw [← map_pow, d4d2sq, map_one]
  have hfe2_ne1 : f d4d2 ≠ 1 := fun h => d4d2ne1 (f.injective (by rw [h, map_one]))
  have hfe2_nez : f d4d2 ≠ d4z := fun h => d4d2nez (f.injective (h.trans hfz.symm))
  have hfe2_cases : f d4d2 = d4d2 ∨ f d4d2 = d4d1 * d4d2 ∨ f d4d2 = d4d1 ^ 2 * d4d2 ∨
      f d4d2 = d4d1 ^ 3 * d4d2 := by
    rcases d4order2_mem (f d4d2) hfe2_sq with h | h | h | h | h | h
    · exact absurd h hfe2_ne1
    · exact absurd h hfe2_nez
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hfe2 : f d4d2 = d4d2 := by
    rcases hfe2_cases with h | h | h | h
    · exact h
    · exfalso
      have hf2 : f (f d4d2) = d4d1 ^ 2 * d4d2 := by rw [h, map_mul, h, hfe1, d4calc1]
      have hf3' : f (f (f d4d2)) = d4d1 ^ 3 * d4d2 := by
        rw [hf2, map_mul, map_pow, hfe1, h, d4calc2]
      have h3' : f (f (f d4d2)) = d4d2 := hfapp d4d2
      rw [hf3'] at h3'
      exact d4d1pow3 (mul_right_cancel (a := d4d1 ^ 3) (b := d4d2) (by rw [one_mul]; exact h3'))
    · exfalso
      have hf2 : f (f d4d2) = d4d2 := by rw [h, map_mul, map_pow, hfe1, h, d4calc3]
      have hf3' : f (f (f d4d2)) = d4d1 ^ 2 * d4d2 := (congrArg f hf2).trans h
      have h3' : f (f (f d4d2)) = d4d2 := hfapp d4d2
      rw [hf3'] at h3'
      exact d4d1sq_ne1 (mul_right_cancel (a := d4d1 ^ 2) (b := d4d2) (by rw [one_mul]; exact h3'))
    · exfalso
      have hf2 : f (f d4d2) = d4d1 ^ 2 * d4d2 := by rw [h, map_mul, map_pow, hfe1, h, d4calc4]
      have hf3' : f (f (f d4d2)) = d4d1 * d4d2 := by
        rw [hf2, map_mul, map_pow, hfe1, h, d4calc5]
      have h3' : f (f (f d4d2)) = d4d2 := hfapp d4d2
      rw [hf3'] at h3'
      exact d4d1ne1 (mul_right_cancel (a := d4d1) (b := d4d2) (by rw [one_mul]; exact h3'))
  apply DFunLike.ext
  intro x
  change f x = x
  rcases d4gen x with h | h | h | h | h | h | h | h <;>
    simp [h, map_pow, map_mul, hfe1, hfe2]

/-! ### `QuaternionGroup 2` and `ElementaryP3 2` genuinely admit order-`3` automorphisms.

Unlike the three types above, `Aut(Q8) ≅ S₄` (order `24`) and `Aut((ZMod 2)³) ≅ GL(3,2)`
(order `168`) both contain order-`3` elements, so the Sylow-2-normal branch has genuinely
new (not-direct-product) semidirect products for these two `H`-types. This section builds
one concrete order-`3` automorphism for each — the classical constructions (cyclically
permuting `i, j, k` for `Q8`; the companion matrix of the irreducible `x² + x + 1` over
`𝔽₂`, fixing one coordinate and rotating the other two, for `(ZMod 2)³`) — each verified by
a *small* `decide` (an `8 × 8` multiplicativity check, nothing like the rejected
`Equiv.Perm`-search scale). Classifying every `φ : P →* MulAut H` up to the
`Aut P × Aut H` orbit moves (i.e. showing every nontrivial one is equivalent to a power of
these) is the remaining, larger piece of this branch — not yet built. -/

open QuaternionGroup in
/-- The cyclic order-`3` automorphism of `Q8` permuting `i ↦ j ↦ k ↦ i` (and correspondingly
`-i ↦ -j ↦ -k ↦ -i`), where `i = a 1`, `j = xa 0`, `k = i * j = xa 3`. -/
def q8CycFun : QuaternionGroup 2 → QuaternionGroup 2
  | .a 0 => .a 0
  | .a 1 => .xa 0
  | .a 2 => .a 2
  | .a 3 => .xa 2
  | .xa 0 => .xa 3
  | .xa 1 => .a 3
  | .xa 2 => .xa 1
  | .xa 3 => .a 1

open QuaternionGroup in
private def q8CycInvFun : QuaternionGroup 2 → QuaternionGroup 2
  | .a 0 => .a 0
  | .a 1 => .xa 3
  | .a 2 => .a 2
  | .a 3 => .xa 1
  | .xa 0 => .a 1
  | .xa 1 => .xa 2
  | .xa 2 => .a 3
  | .xa 3 => .xa 0

private theorem q8Cyc_left_inv : ∀ x : QuaternionGroup 2, q8CycInvFun (q8CycFun x) = x := by decide
private theorem q8Cyc_right_inv : ∀ x : QuaternionGroup 2, q8CycFun (q8CycInvFun x) = x := by
  decide
private theorem q8Cyc_mul : ∀ x y : QuaternionGroup 2, q8CycFun (x * y) = q8CycFun x * q8CycFun y :=
  by decide

/-- The concrete order-`3` automorphism of `Q8`. -/
def q8Cyc : MulAut (QuaternionGroup 2) where
  toFun := q8CycFun
  invFun := q8CycInvFun
  left_inv := q8Cyc_left_inv
  right_inv := q8Cyc_right_inv
  map_mul' := q8Cyc_mul

theorem q8Cyc_apply (x : QuaternionGroup 2) : q8Cyc x = q8CycFun x := rfl

open QuaternionGroup in
theorem q8Cyc_pow3 : q8Cyc ^ 3 = 1 := by
  apply DFunLike.ext
  intro x
  change q8Cyc (q8Cyc (q8Cyc x)) = x
  simp only [q8Cyc_apply]
  revert x
  decide

open QuaternionGroup in
theorem q8Cyc_ne_one : q8Cyc ≠ 1 := by
  intro h
  have heq : q8Cyc (a 1) = a 1 := by rw [h]; rfl
  rw [q8Cyc_apply] at heq
  simp [q8CycFun] at heq

/-- `ElementaryP3 2 ≃ (ZMod 2)³`, realised concretely as a product of three copies of
`Multiplicative (ZMod 2)` (matching how `P3Group.IsP3Group` states the elementary abelian
case). -/
abbrev E8 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

/-- The companion-matrix rotation: fixes the first coordinate, rotates the other two via
the order-`3` element `[[0,1],[1,1]]` of `GL(2,2)` (multiplication by a root of the
irreducible `x² + x + 1` over `𝔽₂`). -/
def e8RotFun : E8 → E8 := fun ⟨p, q, r⟩ => (p, r, q * r)

private def e8RotInvFun : E8 → E8 := fun ⟨p, q, r⟩ => (p, q * r, q)

private theorem e8Rot_left_inv : ∀ x : E8, e8RotInvFun (e8RotFun x) = x := by decide
private theorem e8Rot_right_inv : ∀ x : E8, e8RotFun (e8RotInvFun x) = x := by decide
private theorem e8Rot_mul : ∀ x y : E8, e8RotFun (x * y) = e8RotFun x * e8RotFun y := by decide

/-- The concrete order-`3` automorphism of `(ZMod 2)³`. -/
def e8Rot : MulAut E8 where
  toFun := e8RotFun
  invFun := e8RotInvFun
  left_inv := e8Rot_left_inv
  right_inv := e8Rot_right_inv
  map_mul' := e8Rot_mul

theorem e8Rot_apply (x : E8) : e8Rot x = e8RotFun x := rfl

theorem e8Rot_pow3 : e8Rot ^ 3 = 1 := by
  apply DFunLike.ext
  intro x
  change e8Rot (e8Rot (e8Rot x)) = x
  simp only [e8Rot_apply]
  revert x
  decide

theorem e8Rot_ne_one : e8Rot ≠ 1 := by
  intro h
  have heq : e8Rot (1, Multiplicative.ofAdd (1 : ZMod 2), 1) =
      (1, Multiplicative.ofAdd (1 : ZMod 2), 1) := by rw [h]; rfl
  rw [e8Rot_apply] at heq
  simp [e8RotFun] at heq

/-! ### No order-`9` automorphism of `Q8`: `f⁹ = 1 → f³ = 1`.

This rules out the image of `φ : P →* MulAut Q8` (`P` order `9`) ever hitting an order-`9`
element, leaving only order `1` or `3` — the remaining piece (that every order-`3` `f` is
`Aut(Q8)`-conjugate to a power of `q8Cyc`) is not yet built.

The argument avoids computing `Nat.card (MulAut Q8)` (which would need constructing
`Aut(Q8) ≅ S₄` from scratch): the `6`-element set of order-`4` elements of `Q8` is preserved
by any automorphism, so for `f` with `f⁹ = 1`, `Function.minimalPeriod f x` (for `x` order-`4`)
divides `9` (from `f⁹ = 1`) *and* is at most `6` (the orbit `{x, f x, …}` has
`minimalPeriod` many **distinct** elements, all inside the `6`-element set) — forcing
`minimalPeriod f x ∈ {1, 3}`, hence `f³` fixes `x`. Applying this to both generators
`a 1` and `xa 0` and combining via `map_pow`/`map_mul` gives `f³ = 1` everywhere. -/

open QuaternionGroup in
/-- The `6`-element set of order-`4` elements of `Q8`. -/
private def q8Order4Set : Finset (QuaternionGroup 2) := {a 1, a 3, xa 0, xa 1, xa 2, xa 3}

private theorem q8Order4Set_card : q8Order4Set.card = 6 := by decide

private theorem q8Order4Set_mem_iff : ∀ x : QuaternionGroup 2,
    x ∈ q8Order4Set ↔ x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by decide

private theorem q8Order4Set_preserved (f : MulAut (QuaternionGroup 2)) (y : QuaternionGroup 2)
    (hy : y ∈ q8Order4Set) : f y ∈ q8Order4Set := by
  rw [q8Order4Set_mem_iff] at hy ⊢
  constructor
  · rw [← map_pow, hy.1, map_one]
  · intro hcontra
    rw [← map_pow] at hcontra
    exact hy.2 (f.injective (by rw [hcontra, map_one]))

private theorem q8_pow_apply_eq_iterate (f : MulAut (QuaternionGroup 2)) (n : ℕ)
    (x : QuaternionGroup 2) : (f ^ n) x = f^[n] x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change f ((f ^ k) x) = _
    rw [ih, Function.iterate_succ_apply']

private theorem q8_minimalPeriod_le_six (f : MulAut (QuaternionGroup 2)) (x : QuaternionGroup 2)
    (hx : x ∈ q8Order4Set) : Function.minimalPeriod f x ≤ 6 := by
  have hall : ∀ k, f^[k] x ∈ q8Order4Set := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact q8Order4Set_preserved f _ ih
  have hmaps : Set.MapsTo (fun k => f^[k] x) (Finset.range (Function.minimalPeriod f x) : Set ℕ)
      (q8Order4Set : Set (QuaternionGroup 2)) := fun k _ => hall k
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f :=
  (f : QuaternionGroup 2 → QuaternionGroup 2))
    (x := x)
  have hinj' : ((Finset.range (Function.minimalPeriod f x) : Set ℕ)).InjOn
      (fun k => f^[k] x) := by rwa [Finset.coe_range]
  have hcard := Finset.card_le_card_of_injOn (fun k => f^[k] x) hmaps hinj'
  rwa [Finset.card_range, q8Order4Set_card] at hcard

private theorem q8_fixed_by_pow3_of_order4 (f : MulAut (QuaternionGroup 2)) (hf9 : f ^ 9 = 1)
    (x : QuaternionGroup 2) (hx : x ∈ q8Order4Set) : (f ^ 3) x = x := by
  have hperiodic9 : Function.IsPeriodicPt (⇑f) 9 x := by
    change f^[9] x = x
    rw [← q8_pow_apply_eq_iterate, hf9]
    rfl
  have hdvd9 : Function.minimalPeriod (⇑f) x ∣ 9 := hperiodic9.minimalPeriod_dvd
  have hle6 : Function.minimalPeriod (⇑f) x ≤ 6 := q8_minimalPeriod_le_six f x hx
  have hdvd3 : Function.minimalPeriod (⇑f) x ∣ 3 := by
    interval_cases h : Function.minimalPeriod (⇑f) x <;> omega
  have hp3 : Function.IsPeriodicPt (⇑f) 3 x :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hdvd3
  rw [q8_pow_apply_eq_iterate]
  exact hp3

open QuaternionGroup in
private theorem q8_natCast_val : ∀ i : ZMod 4, ((i.val : ℕ) : ZMod 4) = i := by decide

open QuaternionGroup in
private theorem q8_a_eq_a_one_pow (i : ZMod 4) : (a i : QuaternionGroup 2) = (a 1) ^ i.val := by
  rw [a_one_pow, q8_natCast_val]

open QuaternionGroup in
private theorem q8_xa_eq_xa_zero_mul (i : ZMod 4) :
    (xa i : QuaternionGroup 2) = xa 0 * a i := by rw [xa_mul_a, zero_add]

open QuaternionGroup in
/-- No automorphism of `Q8` has order `9`: `f⁹ = 1` forces `f³ = 1`. -/
theorem q8_pow9_imp_pow3 (f : MulAut (QuaternionGroup 2)) (hf9 : f ^ 9 = 1) : f ^ 3 = 1 := by
  have h1 : (f ^ 3) (a 1) = a 1 := q8_fixed_by_pow3_of_order4 f hf9 (a 1) (by decide)
  have h2 : (f ^ 3) (xa 0) = xa 0 := q8_fixed_by_pow3_of_order4 f hf9 (xa 0) (by decide)
  apply DFunLike.ext
  intro x
  change (f ^ 3) x = x
  rcases x with i | i
  · rw [q8_a_eq_a_one_pow i, map_pow, h1, ← q8_a_eq_a_one_pow]
  · rw [q8_xa_eq_xa_zero_mul i, map_mul, h2, q8_a_eq_a_one_pow i, map_pow, h1,
      ← q8_a_eq_a_one_pow, ← q8_xa_eq_xa_zero_mul]

/-! ### No order-`9` automorphism of `(ZMod 2)³` either: `f⁹ = 1 → f³ = 1`.

Same technique as `Q8`, but since `(ZMod 2)³` is elementary abelian, *every* nonidentity
element has order `2` (no order-`4` elements to single out), so instead we track all `3`
generators through the `7`-element set of *all* nonidentity elements (`7 < 9`, still enough
to force `minimalPeriod ≤ 7`, hence `∈ {1, 3}`, exactly as before). -/

private def e8NonId : Finset E8 := Finset.univ.erase 1

private theorem e8NonId_card : e8NonId.card = 7 := by decide

private theorem e8NonId_mem_iff : ∀ x : E8, x ∈ e8NonId ↔ x ≠ 1 := by decide

private theorem e8NonId_preserved (f : MulAut E8) (y : E8) (hy : y ∈ e8NonId) :
    f y ∈ e8NonId := by
  rw [e8NonId_mem_iff] at hy ⊢
  intro hcontra
  exact hy (f.injective (by rw [hcontra, map_one]))

private theorem e8_pow_apply_eq_iterate (f : MulAut E8) (n : ℕ) (x : E8) :
    (f ^ n) x = f^[n] x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change f ((f ^ k) x) = _
    rw [ih, Function.iterate_succ_apply']

private theorem e8_minimalPeriod_le_seven (f : MulAut E8) (x : E8) (hx : x ∈ e8NonId) :
    Function.minimalPeriod f x ≤ 7 := by
  have hall : ∀ k, f^[k] x ∈ e8NonId := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact e8NonId_preserved f _ ih
  have hmaps : Set.MapsTo (fun k => f^[k] x) (Finset.range (Function.minimalPeriod f x) : Set ℕ)
      (e8NonId : Set E8) := fun k _ => hall k
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := (f : E8 → E8)) (x := x)
  have hinj' : ((Finset.range (Function.minimalPeriod f x) : Set ℕ)).InjOn
      (fun k => f^[k] x) := by rwa [Finset.coe_range]
  have hcard := Finset.card_le_card_of_injOn (fun k => f^[k] x) hmaps hinj'
  rwa [Finset.card_range, e8NonId_card] at hcard

private theorem e8_fixed_by_pow3_of_nonId (f : MulAut E8) (hf9 : f ^ 9 = 1) (x : E8)
    (hx : x ∈ e8NonId) : (f ^ 3) x = x := by
  have hperiodic9 : Function.IsPeriodicPt (⇑f) 9 x := by
    change f^[9] x = x
    rw [← e8_pow_apply_eq_iterate, hf9]
    rfl
  have hdvd9 : Function.minimalPeriod (⇑f) x ∣ 9 := hperiodic9.minimalPeriod_dvd
  have hle7 : Function.minimalPeriod (⇑f) x ≤ 7 := e8_minimalPeriod_le_seven f x hx
  have hdvd3 : Function.minimalPeriod (⇑f) x ∣ 3 := by
    interval_cases h : Function.minimalPeriod (⇑f) x <;> omega
  have hp3 : Function.IsPeriodicPt (⇑f) 3 x :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hdvd3
  rw [e8_pow_apply_eq_iterate]
  exact hp3

private def e8g1 : E8 := (Multiplicative.ofAdd (1 : ZMod 2), 1, 1)
private def e8g2 : E8 := (1, Multiplicative.ofAdd (1 : ZMod 2), 1)
private def e8g3 : E8 := (1, 1, Multiplicative.ofAdd (1 : ZMod 2))

private theorem e8gen : ∀ x : E8, x = 1 ∨ x = e8g1 ∨ x = e8g2 ∨ x = e8g3 ∨ x = e8g1 * e8g2 ∨
    x = e8g1 * e8g3 ∨ x = e8g2 * e8g3 ∨ x = e8g1 * e8g2 * e8g3 := by decide

/-- No automorphism of `(ZMod 2)³` has order `9`: `f⁹ = 1` forces `f³ = 1`. -/
theorem e8_pow9_imp_pow3 (f : MulAut E8) (hf9 : f ^ 9 = 1) : f ^ 3 = 1 := by
  have h1 : (f ^ 3) e8g1 = e8g1 := e8_fixed_by_pow3_of_nonId f hf9 e8g1 (by decide)
  have h2 : (f ^ 3) e8g2 = e8g2 := e8_fixed_by_pow3_of_nonId f hf9 e8g2 (by decide)
  have h3 : (f ^ 3) e8g3 = e8g3 := e8_fixed_by_pow3_of_nonId f hf9 e8g3 (by decide)
  apply DFunLike.ext
  intro x
  change (f ^ 3) x = x
  rcases e8gen x with h | h | h | h | h | h | h | h <;>
    simp [h, map_mul, h1, h2, h3]

/-! ### Toward exhaustiveness for `Q8`: no order-`3` automorphism fixes the "axis" `a 1`
(nor sends it to `a 1⁻¹ = a 3`).

This is the first real step of the conjugacy-classification of order-`3` automorphisms of
`Q8` (classically: `Aut(Q8) ≅ S₄` acts on the three antipodal pairs `{±i,±j,±k}` as `S₃`, and
an order-`3` element of `S₄` must act on those three pairs as a genuine `3`-cycle — it cannot
fix a pair). Both halves are proved directly by generator-orbit tracking through `f`, `f²`,
`f³ = 1`, with no automorphism-group search. -/

open QuaternionGroup in
private theorem q8order4_mem : ∀ x : QuaternionGroup 2, x ^ 4 = 1 → x ^ 2 ≠ 1 →
    (x = a 1 ∨ x = a 3 ∨ x = xa 0 ∨ x = xa 1 ∨ x = xa 2 ∨ x = xa 3) := by decide

open QuaternionGroup in
private theorem q8gen : ∀ x : QuaternionGroup 2, x = 1 ∨ x = a 1 ∨ x = a 1 ^ 2 ∨ x = a 1 ^ 3 ∨
    x = xa 0 ∨ x = xa 0 * a 1 ∨ x = xa 0 * a 1 ^ 2 ∨ x = xa 0 * a 1 ^ 3 := by decide

open QuaternionGroup in
private theorem q8_xa1_eq : (xa 1 : QuaternionGroup 2) = xa 0 * a 1 := by decide
open QuaternionGroup in
private theorem q8_xa2_eq : (xa 2 : QuaternionGroup 2) = xa 0 * a 1 ^ 2 := by decide
open QuaternionGroup in
private theorem q8_xa3_eq : (xa 3 : QuaternionGroup 2) = xa 0 * a 1 ^ 3 := by decide

open QuaternionGroup in
private theorem q8calc1 : xa 0 * a 1 * a 1 = xa 0 * (a 1 : QuaternionGroup 2) ^ 2 := by decide
open QuaternionGroup in
private theorem q8calc2 : xa 0 * a 1 * a 1 ^ 2 = xa 0 * (a 1 : QuaternionGroup 2) ^ 3 := by decide
open QuaternionGroup in
private theorem q8calc3 : xa 0 * a 1 ^ 2 * a 1 ^ 2 = (xa 0 : QuaternionGroup 2) := by decide
open QuaternionGroup in
private theorem q8calc4 : xa 0 * a 1 ^ 3 * a 1 ^ 3 = xa 0 * (a 1 : QuaternionGroup 2) ^ 2 := by
  decide
open QuaternionGroup in
private theorem q8calc5 : xa 0 * a 1 ^ 3 * a 1 ^ 2 = xa 0 * (a 1 : QuaternionGroup 2) := by decide

open QuaternionGroup in
/-- No order-`3` automorphism of `Q8` sends `a 1` (`= i`) to `a 3` (`= i⁻¹ = -i`). -/
theorem q8_order3_fa1_ne_a3 (f : MulAut (QuaternionGroup 2)) (hf3 : f ^ 3 = 1) :
    f (a 1) ≠ a 3 := by
  intro heq
  have hfapp : ∀ g : QuaternionGroup 2, (f ^ 3) g = g := by intro g; rw [hf3]; rfl
  have hfa3 : f (a 3) = a 1 := by
    have h13 : (a 3 : QuaternionGroup 2) = (a 1) ^ 3 := by decide
    rw [h13, map_pow, heq]; decide
  have h3 : f (f (f (a 1))) = a 1 := hfapp (a 1)
  rw [heq, hfa3, heq] at h3
  exact absurd h3 (by decide)

open QuaternionGroup in
/-- No **nontrivial** order-`3` automorphism of `Q8` fixes `a 1` (`= i`). Combined with
`q8_order3_fa1_ne_a3`, every nontrivial order-`3` `f` sends `a 1` to one of the four
`X`-type order-`4` elements `xa 0, xa 1, xa 2, xa 3`. -/
theorem q8_order3_fa1_ne_a1 (f : MulAut (QuaternionGroup 2)) (hf3 : f ^ 3 = 1)
    (hfne1 : f ≠ 1) : f (a 1) ≠ a 1 := by
  intro heq
  have hfapp : ∀ g : QuaternionGroup 2, (f ^ 3) g = g := by intro g; rw [hf3]; rfl
  have hfa3 : f (a 3) = a 3 := by
    have h13 : (a 3 : QuaternionGroup 2) = (a 1) ^ 3 := by decide
    rw [h13, map_pow, heq]
  have hxa0_4 : (f (xa 0)) ^ 4 = 1 := by
    have h1 : (xa 0 : QuaternionGroup 2) ^ 4 = 1 := by decide
    rw [← map_pow, h1, map_one]
  have hxa0_sqne1 : (f (xa 0)) ^ 2 ≠ 1 := by
    have hne : (xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
    rw [← map_pow]
    intro hc
    exact hne (f.injective (by rw [hc, map_one]))
  rcases q8order4_mem (f (xa 0)) hxa0_4 hxa0_sqne1 with h | h | h | h | h | h
  · exact absurd (f.injective (h.trans heq.symm)) (by decide)
  · exact absurd (f.injective (h.trans hfa3.symm)) (by decide)
  · apply hfne1
    have hfa2 : f (a 2) = a 2 := by
      have ha2 : (a 2 : QuaternionGroup 2) = a 1 ^ 2 := by decide
      rw [ha2, map_pow, heq]
    have hfxa1 : f (xa 1) = xa 1 := by rw [q8_xa1_eq, map_mul, h, heq]
    have hfxa2 : f (xa 2) = xa 2 := by rw [q8_xa2_eq, map_mul, map_pow, h, heq]
    have hfxa3 : f (xa 3) = xa 3 := by rw [q8_xa3_eq, map_mul, map_pow, h, heq]
    apply DFunLike.ext
    intro x
    change f x = x
    rcases q8gen x with hx | hx | hx | hx | hx | hx | hx | hx <;>
      (rw [hx]; first | exact map_one f | exact heq | exact hfa2 | exact hfa3 | exact h | exact hfxa1 | exact hfxa2 | exact hfxa3)
  · rw [q8_xa1_eq] at h
    have hf2 : f (f (xa 0)) = xa 0 * a 1 ^ 2 := by
      rw [h, map_mul, h, heq]; exact q8calc1
    have hf3' : f (f (f (xa 0))) = xa 0 * a 1 ^ 3 := by
      rw [hf2, map_mul, map_pow, h, heq]; exact q8calc2
    have hcontra : f (f (f (xa 0))) = xa 0 := hfapp (xa 0)
    rw [hf3'] at hcontra
    have heq2 : xa 0 * (a 1 : QuaternionGroup 2) ^ 3 = xa 0 * 1 := by
      rw [mul_one]; exact hcontra
    exact absurd (mul_left_cancel heq2) (by decide)
  · rw [q8_xa2_eq] at h
    have hf2 : f (f (xa 0)) = xa 0 := by
      rw [h, map_mul, h, map_pow, heq]; exact q8calc3
    have hf3' : f (f (f (xa 0))) = xa 0 * a 1 ^ 2 := by rw [hf2]; exact h
    have hcontra : f (f (f (xa 0))) = xa 0 := hfapp (xa 0)
    rw [hf3'] at hcontra
    have heq2 : xa 0 * (a 1 : QuaternionGroup 2) ^ 2 = xa 0 * 1 := by
      rw [mul_one]; exact hcontra
    exact absurd (mul_left_cancel heq2) (by decide)
  · rw [q8_xa3_eq] at h
    have hf2 : f (f (xa 0)) = xa 0 * a 1 ^ 2 := by
      rw [h, map_mul, h, map_pow, heq]; exact q8calc4
    have hf3' : f (f (f (xa 0))) = xa 0 * a 1 := by
      rw [hf2, map_mul, map_pow, h, heq]; exact q8calc5
    have hcontra : f (f (f (xa 0))) = xa 0 := hfapp (xa 0)
    rw [hf3'] at hcontra
    have heq2 : xa 0 * (a 1 : QuaternionGroup 2) = xa 0 * 1 := by
      rw [mul_one]; exact hcontra
    exact absurd (mul_left_cancel heq2) (by decide)

open QuaternionGroup in
/-- Every nontrivial order-`3` automorphism of `Q8` sends `a 1` to one of the four
`X`-type order-`4` elements. -/
theorem q8_order3_fa1_mem (f : MulAut (QuaternionGroup 2)) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    f (a 1) = xa 0 ∨ f (a 1) = xa 1 ∨ f (a 1) = xa 2 ∨ f (a 1) = xa 3 := by
  have h4 : (f (a 1)) ^ 4 = 1 := by
    have h1 : (a 1 : QuaternionGroup 2) ^ 4 = 1 := by decide
    rw [← map_pow, h1, map_one]
  have hsqne1 : (f (a 1)) ^ 2 ≠ 1 := by
    have hne : (a 1 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
    rw [← map_pow]
    intro hc
    exact hne (f.injective (by rw [hc, map_one]))
  rcases q8order4_mem (f (a 1)) h4 hsqne1 with h | h | h | h | h | h
  · exact absurd h (q8_order3_fa1_ne_a1 f hf3 hfne1)
  · exact absurd h (q8_order3_fa1_ne_a3 f hf3)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-! ### The "generation formula": every automorphism of `Q8` is determined by where it sends
the two generators `a 1` and `xa 0`, via `f (a k) = f (a 1) ^ k` and
`f (xa k) = f (xa 0) * f (a 1) ^ k`. This reduces "classify `f` up to conjugacy" to a
finite search over the (small) set of valid `(f (a 1), f (xa 0))` pairs — no automorphism-group
enumeration needed. -/

open QuaternionGroup in
private theorem q8_ak_eq : ∀ k : ZMod 4, (a k : QuaternionGroup 2) = (a 1) ^ k.val := by decide

open QuaternionGroup in
private theorem q8_xak_eq : ∀ k : ZMod 4, (xa k : QuaternionGroup 2) = xa 0 * (a 1) ^ k.val := by
  decide

open QuaternionGroup in
theorem q8_f_ak (f : MulAut (QuaternionGroup 2)) (k : ZMod 4) :
    f (a k) = (f (a 1)) ^ k.val := by rw [q8_ak_eq, map_pow]

open QuaternionGroup in
theorem q8_f_xak (f : MulAut (QuaternionGroup 2)) (k : ZMod 4) :
    f (xa k) = f (xa 0) * (f (a 1)) ^ k.val := by rw [q8_xak_eq, map_mul, map_pow]

open QuaternionGroup in
/-- The purely computational model of a `Q8`-endomorphism determined by where it sends the two
generators: `q8ext A' X'` is the function that would result from extending `a 1 ↦ A'`,
`xa 0 ↦ X'` via the generation relations. -/
private def q8ext (A' X' : QuaternionGroup 2) : QuaternionGroup 2 → QuaternionGroup 2
  | .a k => A' ^ k.val
  | .xa k => X' * A' ^ k.val

/-- Build the `MulAut` corresponding to a valid `(A', X')` pair: `q8ext A' X'` is already a
homomorphism (`hHom`, checked by a small `decide`) and injective (`hInj`, ditto), hence
bijective on the finite `Q8` — this packages it as a genuine automorphism, reusable for every
conjugator we need below (avoiding a bespoke `toFun`/`invFun` table each time, unlike `q8Cyc`).
-/
private noncomputable def q8BuildAut (A' X' : QuaternionGroup 2)
    (hHom : ∀ x y, q8ext A' X' (x * y) = q8ext A' X' x * q8ext A' X' y)
    (hInj : Function.Injective (q8ext A' X')) : MulAut (QuaternionGroup 2) :=
  MulEquiv.ofBijective (MonoidHom.mk' (q8ext A' X') hHom)
    (Finite.injective_iff_bijective.mp hInj)

private theorem q8BuildAut_apply (A' X' : QuaternionGroup 2) (hHom hInj) (x : QuaternionGroup 2) :
    q8BuildAut A' X' hHom hInj x = q8ext A' X' x := rfl

open QuaternionGroup in
/-- Every automorphism agrees with the `q8ext` model built from its own values on the two
generators. -/
private theorem q8_f_eq_ext (f : MulAut (QuaternionGroup 2)) (x : QuaternionGroup 2) :
    f x = q8ext (f (a 1)) (f (xa 0)) x := by
  cases x with
  | a k => exact q8_f_ak f k
  | xa k => exact q8_f_xak f k

open QuaternionGroup in
/-- Small closed-form computation (`4 × 6 = 24` concrete pairs, nothing like a full
automorphism-group search) pinning `f (xa 0)` once `f (a 1)` and the order-`3` condition are
known. -/
private theorem q8_pin_decide : ∀ A' X' : QuaternionGroup 2,
    (A' = xa 0 ∨ A' = xa 1 ∨ A' = xa 2 ∨ A' = xa 3) →
    (X' = a 1 ∨ X' = a 3 ∨ X' = xa 0 ∨ X' = xa 1 ∨ X' = xa 2 ∨ X' = xa 3) →
    (q8ext A' X' (q8ext A' X' (q8ext A' X' (a 1))) = a 1 ∧
     q8ext A' X' (q8ext A' X' (q8ext A' X' (xa 0))) = xa 0) →
    (A' = xa 0 ∧ (X' = xa 1 ∨ X' = xa 3)) ∨
    (A' = xa 1 ∧ (X' = a 1 ∨ X' = a 3)) ∨
    (A' = xa 2 ∧ (X' = xa 1 ∨ X' = xa 3)) ∨
    (A' = xa 3 ∧ (X' = a 1 ∨ X' = a 3)) := by decide

open QuaternionGroup in
/-- Full pin: for a nontrivial order-`3` automorphism of `Q8`, `(f (a 1), f (xa 0))` is one of
exactly eight pairs (matching the eight order-`3` elements of `Aut(Q8) ≅ S₄`). -/
theorem q8_order3_pin (f : MulAut (QuaternionGroup 2)) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    (f (a 1) = xa 0 ∧ (f (xa 0) = xa 1 ∨ f (xa 0) = xa 3)) ∨
    (f (a 1) = xa 1 ∧ (f (xa 0) = a 1 ∨ f (xa 0) = a 3)) ∨
    (f (a 1) = xa 2 ∧ (f (xa 0) = xa 1 ∨ f (xa 0) = xa 3)) ∨
    (f (a 1) = xa 3 ∧ (f (xa 0) = a 1 ∨ f (xa 0) = a 3)) := by
  have hmem := q8_order3_fa1_mem f hf3 hfne1
  have hx4 : (f (xa 0)) ^ 4 = 1 := by
    have h1 : (xa 0 : QuaternionGroup 2) ^ 4 = 1 := by decide
    rw [← map_pow, h1, map_one]
  have hxsqne1 : (f (xa 0)) ^ 2 ≠ 1 := by
    have hne : (xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
    rw [← map_pow]
    intro hc
    exact hne (f.injective (by rw [hc, map_one]))
  have hxmem := q8order4_mem (f (xa 0)) hx4 hxsqne1
  have stepx1 : q8ext (f (a 1)) (f (xa 0)) (xa 0) = f (xa 0) := (q8_f_eq_ext f (xa 0)).symm
  have stepx2 : q8ext (f (a 1)) (f (xa 0)) (f (xa 0)) = f (f (xa 0)) :=
    (q8_f_eq_ext f (f (xa 0))).symm
  have stepx3 : q8ext (f (a 1)) (f (xa 0)) (f (f (xa 0))) = f (f (f (xa 0))) :=
    (q8_f_eq_ext f (f (f (xa 0)))).symm
  have stepa1 : q8ext (f (a 1)) (f (xa 0)) (a 1) = f (a 1) := (q8_f_eq_ext f (a 1)).symm
  have stepa2 : q8ext (f (a 1)) (f (xa 0)) (f (a 1)) = f (f (a 1)) :=
    (q8_f_eq_ext f (f (a 1))).symm
  have stepa3 : q8ext (f (a 1)) (f (xa 0)) (f (f (a 1))) = f (f (f (a 1))) :=
    (q8_f_eq_ext f (f (f (a 1)))).symm
  have happx : f (f (f (xa 0))) = xa 0 := by
    have h : (f ^ 3) (xa 0) = xa 0 := by rw [hf3]; rfl
    exact h
  have happa : f (f (f (a 1))) = a 1 := by
    have h : (f ^ 3) (a 1) = a 1 := by rw [hf3]; rfl
    exact h
  have h3x : q8ext (f (a 1)) (f (xa 0)) (q8ext (f (a 1)) (f (xa 0))
      (q8ext (f (a 1)) (f (xa 0)) (xa 0))) = xa 0 := by
    rw [stepx1, stepx2, stepx3]; exact happx
  have h3a : q8ext (f (a 1)) (f (xa 0)) (q8ext (f (a 1)) (f (xa 0))
      (q8ext (f (a 1)) (f (xa 0)) (a 1))) = a 1 := by
    rw [stepa1, stepa2, stepa3]; exact happa
  exact q8_pin_decide (f (a 1)) (f (xa 0)) hmem hxmem ⟨h3a, h3x⟩

open QuaternionGroup in
private theorem q8Cyc_eq_ext (x : QuaternionGroup 2) : q8Cyc x = q8ext (xa 0) (xa 3) x := by
  have h := q8_f_eq_ext q8Cyc x
  rwa [show q8Cyc (a 1) = xa 0 from rfl, show q8Cyc (xa 0) = xa 3 from rfl] at h

open QuaternionGroup in
/-- Every nontrivial order-`3` automorphism of `Q8` is `Aut(Q8)`-conjugate to `q8Cyc`. Combined
with `q8Cyc_pow3`/`q8Cyc_ne_one`, this completes the order-`3` conjugacy classification for
`Q8`: exhaustiveness at the "genuinely new action" case of the Sylow-2-normal branch. -/
theorem q8_order3_conj_to_cyc (f : MulAut (QuaternionGroup 2)) (hf3 : f ^ 3 = 1)
    (hfne1 : f ≠ 1) : ∃ g : MulAut (QuaternionGroup 2), g * f * g⁻¹ = q8Cyc := by
  have hpin := q8_order3_pin f hf3 hfne1
  -- Given a valid conjugator `(gA, gX)` for the pinned pair `(f (a 1), f (xa 0))`, package it
  -- into the conclusion.
  suffices h : ∃ gA gX : QuaternionGroup 2,
      ∃ hHom : ∀ x y, q8ext gA gX (x * y) = q8ext gA gX x * q8ext gA gX y,
      ∃ hInj : Function.Injective (q8ext gA gX),
      ∀ x, q8ext gA gX (f x) = q8ext (xa 0) (xa 3) (q8ext gA gX x) by
    obtain ⟨gA, gX, hHom, hInj, hconj⟩ := h
    refine ⟨q8BuildAut gA gX hHom hInj, ?_⟩
    set g := q8BuildAut gA gX hHom hInj with hgdef
    apply DFunLike.ext
    intro x
    change g (f (g⁻¹ x)) = q8Cyc x
    rw [q8Cyc_eq_ext]
    have e1 : g (f (g⁻¹ x)) = q8ext gA gX (f (g⁻¹ x)) := q8BuildAut_apply gA gX hHom hInj _
    have e2 : q8ext gA gX (g⁻¹ x) = g (g⁻¹ x) := (q8BuildAut_apply gA gX hHom hInj _).symm
    have hgg : g (g⁻¹ x) = x := by simp
    rw [e1, hconj (g⁻¹ x), e2, hgg]
  rcases hpin with ⟨hA, hX | hX⟩ | ⟨hA, hX | hX⟩ | ⟨hA, hX | hX⟩ | ⟨hA, hX | hX⟩
  · -- (xa0, xa1): conjugator (xa1, a3)
    refine ⟨xa 1, a 3, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa0, xa3) = q8Cyc itself: trivial conjugator (identity)
    refine ⟨a 1, xa 0, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa1, a1): conjugator (xa0, a1)
    refine ⟨xa 0, a 1, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa1, a3): conjugator (xa1, xa0)
    refine ⟨xa 1, xa 0, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa2, xa1): conjugator (xa1, a1)
    refine ⟨xa 1, a 1, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa2, xa3): conjugator (xa0, xa1)
    refine ⟨xa 0, xa 1, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa3, a1): conjugator (xa1, xa2)
    refine ⟨xa 1, xa 2, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa3, a3) = q8Cyc²: conjugator (a1, xa1)
    refine ⟨a 1, xa 1, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide

/-! ### `E8` order-`3` conjugacy classification: every nontrivial order-`3` automorphism of
`(ZMod 2)³` has a UNIQUE nontrivial fixed point.

Unlike `Q8` (only `8` order-`3` automorphisms, handled by hand), `E8` has `56`, too many to
case-split explicitly. Instead: `Fix(f) := {x | f x = x}` is a subgroup of `E8`, so
`Nat.card (Fix f) ∣ 8` (Lagrange). The cyclic group `⟨f⟩` (order `3`, since `f³=1 ∧ f≠1`) acts
on the `8`-element set `E8`, so `Nat.card E8 ≡ Nat.card (Fix f) [MOD 3]`
(`IsPGroup.card_modEq_card_fixedPoints`), i.e. `Nat.card (Fix f) ≡ 2 [MOD 3]`. Combined with
`Nat.card (Fix f) ∣ 8` and `f ≠ 1` (so `Nat.card (Fix f) ≠ 8`), the only divisor of `8` that is
`≡ 2 mod 3` and `≠ 8` is `2` — giving a UNIQUE nontrivial fixed point. -/

private def e8Fix (f : MulAut E8) : Subgroup E8 where
  carrier := {x | f x = x}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := map_one f
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

private theorem e8Fix_card_dvd (f : MulAut E8) : Nat.card (e8Fix f) ∣ 8 := by
  have h := Subgroup.card_subgroup_dvd_card (e8Fix f)
  have hE8 : Nat.card E8 = 8 := Nat.card_eq_fintype_card.trans (by decide)
  rwa [hE8] at h

private theorem e8_orderOf_three (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    orderOf f = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime hf3 hfne1

private def e8Gf (f : MulAut E8) : Subgroup (MulAut E8) := Subgroup.zpowers f

private theorem e8Gf_card (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    Nat.card (e8Gf f) = 3 := by
  rw [e8Gf, Nat.card_zpowers, e8_orderOf_three f hf3 hfne1]

private theorem e8Gf_isPGroup (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    IsPGroup 3 (e8Gf f) :=
  IsPGroup.of_card (n := 1) (by rw [e8Gf_card f hf3 hfne1, pow_one])

private theorem e8Gf_mem_iff (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1)
    (m : MulAut E8) : m ∈ e8Gf f ↔ m = 1 ∨ m = f ∨ m = f ^ 2 := by
  classical
  rw [e8Gf, mem_zpowers_iff_mem_range_orderOf, e8_orderOf_three f hf3 hfne1]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk3, rfl⟩
    interval_cases k
    · exact Or.inl (by rfl)
    · exact Or.inr (Or.inl (by rfl))
    · exact Or.inr (Or.inr (by rfl))
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, by rfl⟩
    · exact ⟨1, by norm_num, by rfl⟩
    · exact ⟨2, by norm_num, by rfl⟩

private theorem e8Fix_eq_fixedPoints (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    (MulAction.fixedPoints (e8Gf f) E8) = (e8Fix f : Set E8) := by
  ext x
  simp only [MulAction.fixedPoints, Set.mem_setOf_eq, e8Fix, Subgroup.coe_set_mk]
  constructor
  · intro h
    have hgen : (f : MulAut E8) ∈ e8Gf f := Subgroup.mem_zpowers f
    have := h ⟨f, hgen⟩
    rwa [MulAction.subgroup_smul_def, MulAut.smul_def] at this
  · intro hx m
    rw [MulAction.subgroup_smul_def, MulAut.smul_def]
    rcases (e8Gf_mem_iff f hf3 hfne1 m).mp m.2 with hm | hm | hm
    · show (m : MulAut E8) x = x
      rw [hm]; rfl
    · show (m : MulAut E8) x = x
      rw [hm]; exact hx
    · show (m : MulAut E8) x = x
      rw [hm, e8_pow_apply_eq_iterate]
      show f (f x) = x
      rw [hx, hx]

private theorem e8Fix_card_two (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    Nat.card (e8Fix f) = 2 := by
  have hcong : Nat.card E8 ≡ Nat.card (MulAction.fixedPoints (e8Gf f) E8) [MOD 3] :=
    (e8Gf_isPGroup f hf3 hfne1).card_modEq_card_fixedPoints E8
  rw [e8Fix_eq_fixedPoints f hf3 hfne1] at hcong
  have hE8card : Nat.card E8 = 8 := Nat.card_eq_fintype_card.trans (by decide)
  rw [hE8card] at hcong
  have hmod : Nat.card (e8Fix f) % 3 = 2 := by
    have h : (8 : ℕ) % 3 = Nat.card (e8Fix f) % 3 := hcong
    omega
  have hdvd := e8Fix_card_dvd f
  have hne8 : Nat.card (e8Fix f) ≠ 8 := by
    intro hc
    apply hfne1
    have htop : e8Fix f = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hc]
      exact (Nat.card_eq_fintype_card.trans (by decide) : Nat.card E8 = 8).symm
    apply DFunLike.ext
    intro x
    have hxmem : x ∈ e8Fix f := htop ▸ Subgroup.mem_top x
    exact hxmem
  have hle : Nat.card (e8Fix f) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card (e8Fix f) <;> omega

end Smallgroups.UsefulTheorems
