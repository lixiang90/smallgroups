/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Smallgroups.UsefulTheorems.PrimePairDihedral
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.CenterInvariant
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow

/-!
# Classification of groups of order `2pq` (`2 < p < q` odd primes)

Every group of order `2pq` has a normal subgroup `N` of order `pq` (index `2`). By
Schur–Zassenhaus, `G ≅ N ⋊ ℤ/2`.

The subgroup `N` (order `pq`, `p < q`) is either cyclic (`ℤ/pq`) or, when `p ∣ q - 1`, possibly
non-abelian (`ℤ/q ⋊ ℤ/p`).

## When `¬ p ∣ q - 1`: **4 classes**

`N` is forced to be cyclic (`ℤ/pq`), and the involutory actions `ℤ/2 → Aut(ℤ/pq)` give:
- Type I: `ℤ/2pq` (trivial action)
- Type II: `D_{pq}` (inversion action)
- Type III: `ℤ/q × D_p` (invert the `ℤ/p` factor only)
- Type IV: `ℤ/p × D_q` (invert the `ℤ/q` factor only)

## When `p ∣ q - 1`: **6 classes**

Types I–IV remain, and two additional groups arise from `N ≅ ℤ/q ⋊ ℤ/p`:
- Type V: `(ℤ/q ⋊ ℤ/p) × ℤ/2` (trivial action on the non-abelian `N`)
- Type VI: `ℤ/q ⋊ ℤ/2p` (a faithful action of `ℤ/2p` on `ℤ/q`)

## Status

**Skeleton in progress.** The representative cardinalities, the normal subgroup of order `pq`, the
Schur--Zassenhaus semidirect reduction, and the required unit-existence lemmas are proved; the
exhaustiveness and most distinctness theorems are still marked for future proof.
-/

namespace Smallgroups.UsefulTheorems

open Subgroup

variable (p q : ℕ)

/-! ### Representative types (always present) -/

/-- Type I: `ℤ/2pq` (cyclic). -/
abbrev twoPQ_I : Type := CyclicRep (2 * p * q)

/-- Type II: `D_{pq}` (dihedral group of order `2pq`). -/
abbrev twoPQ_II : Type := DihedralGroup (p * q)

/-- Type III: `ℤ/q × D_p` (direct product). -/
abbrev twoPQ_III : Type := Multiplicative (ZMod q) × DihedralGroup p

/-- Type IV: `ℤ/p × D_q` (direct product). -/
abbrev twoPQ_IV : Type := Multiplicative (ZMod p) × DihedralGroup q

/-! ### Representative types (present when `p ∣ q - 1`) -/

/-- Type V: `(ℤ/q ⋊ ℤ/p) × ℤ/2`. The non-abelian group of order `pq` crossed with `ℤ/2`.
    Here `c : (ZMod q)ˣ` is a unit of order `p` (exists since `p ∣ q - 1`).
    `NonabRep c hc` gives `ℤ/q ⋊ ℤ/p` (implicit p of NonabRep = our q, implicit q = our p). -/
noncomputable abbrev twoPQ_V [NeZero p] (c : (ZMod q)ˣ) (hc : c ^ p = 1) : Type :=
  NonabRep c hc × Multiplicative (ZMod 2)

/-- Type VI: `ℤ/q ⋊ ℤ/2p`. A faithful action of `ℤ/2p` on `ℤ/q` by a unit of order `2p`.
    Here `d : (ZMod q)ˣ` is a unit of order `2p` (exists since `2p ∣ q - 1`).
    `NonabRep d hd` gives `ℤ/q ⋊ ℤ/2p` (implicit p of NonabRep = our q, implicit q = 2·p). -/
noncomputable abbrev twoPQ_VI [NeZero (2 * p)] (d : (ZMod q)ˣ) (hd : d ^ (2 * p) = 1) : Type :=
  NonabRep d hd

/-! ### Cardinalities -/

theorem card_twoPQ_I (hp : p.Prime) (hq : q.Prime) :
    Nat.card (twoPQ_I p q) = 2 * p * q := by
  exact card_cyclicRep (Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hp.ne_zero) hq.ne_zero)

theorem card_twoPQ_II (hp : p.Prime) (hq : q.Prime) :
    Nat.card (twoPQ_II p q) = 2 * p * q := by
  rw [twoPQ_II, DihedralGroup.nat_card]
  have := hp.pos; have := hq.pos; ring

theorem card_twoPQ_III (hq : q.Prime) : Nat.card (twoPQ_III p q) = 2 * p * q := by
  rw [Nat.card_prod, card_cyclicRep hq.pos.ne', DihedralGroup.nat_card]
  ring

theorem card_twoPQ_IV (hp : p.Prime) : Nat.card (twoPQ_IV p q) = 2 * p * q := by
  rw [Nat.card_prod, card_cyclicRep hp.pos.ne', DihedralGroup.nat_card]
  ring

theorem card_twoPQ_V [NeZero p] (c : (ZMod q)ˣ) (hc : c ^ p = 1)
    (_hp : p.Prime) (hq : q.Prime) :
    Nat.card (twoPQ_V p q c hc) = 2 * p * q := by
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  rw [Nat.card_prod, card_nonabRep, card_cyclicRep (by norm_num : (2 : ℕ) ≠ 0)]
  ring

theorem card_twoPQ_VI [NeZero (2 * p)] (d : (ZMod q)ˣ) (hd : d ^ (2 * p) = 1)
    (hq : q.Prime) :
    Nat.card (twoPQ_VI p q d hd) = 2 * p * q := by
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  rw [twoPQ_VI, card_nonabRep]
  ring

/-! ### Key structural lemma -/

variable {G : Type*} [Group G]

private lemma sign_mulLeft_of_orderOf_two [Fintype G] [DecidableEq G]
    (a : G) (ha : orderOf a = 2) (hcard : Odd (Nat.card G / 2)) :
    Equiv.Perm.sign (Equiv.mulLeft a) = -1 := by
  classical
  have ha2 : a ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ha]
  have hperm2 : (Equiv.mulLeft a : Equiv.Perm G) ^ 2 = 1 := by
    ext x
    change a * (a * x) = x
    rw [← mul_assoc, ← pow_two, ha2, one_mul]
  rw [Equiv.Perm.sign_of_pow_two_eq_one hperm2]
  have hfixed : Fintype.card (Function.fixedPoints (Equiv.mulLeft a : Equiv.Perm G)) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨x, hx⟩
    have : a * x = x := hx
    have ha1 : a = 1 := by
      simpa using congr_arg (fun y => y * x⁻¹) this
    have : orderOf a = 1 := by simp [ha1]
    omega
  rw [hfixed, tsub_zero]
  rw [Nat.card_eq_fintype_card] at hcard
  exact hcard.neg_one_pow

/-- Every group of order `2pq` (`2 < p < q`, `p`, `q` odd primes) has a normal subgroup of
    order `pq`.

The proof uses the sign of the left regular action. Since `|G|` is even, Cauchy's theorem gives an
element of order `2`; left multiplication by this element is a fixed-point-free involution, hence an
odd permutation because `|G| / 2 = pq` is odd. Thus the sign homomorphism is onto `ℤˣ`, and its
kernel has index `2`. -/
theorem twoPQ_normal_pq_subgroup (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    [Finite G] (hG : Nat.card G = 2 * p * q) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = p * q := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let χ : G →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom G G)
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hhalf : Nat.card G / 2 = p * q := by
    rw [hG]
    rw [show 2 * p * q = p * q * 2 by ring]
    exact Nat.mul_div_left (p * q) (by norm_num : 0 < 2)
  have hhalfodd : Odd (Nat.card G / 2) := hhalf.symm ▸ hpodd.mul hqodd
  have htwo_dvd : 2 ∣ Nat.card G := by
    refine ⟨p * q, ?_⟩
    rw [hG]
    ring
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 htwo_dvd
  have hχa : χ a = -1 := by
    change Equiv.Perm.sign (MulAction.toPermHom G G a) = -1
    have hperm : MulAction.toPermHom G G a = Equiv.mulLeft a := by
      ext x
      rfl
    rw [hperm]
    exact sign_mulLeft_of_orderOf_two a ha hhalfodd
  have hχsurj : Function.Surjective χ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one χ⟩
    · exact ⟨a, hχa⟩
  have hindex : χ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective χ hχsurj]
    simp [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hNcard : Nat.card χ.ker = p * q := by
    have hmul : Nat.card χ.ker * 2 = Nat.card G := by
      simpa [hindex] using χ.ker.card_mul_index
    apply Nat.mul_right_cancel (m := 2) (by norm_num : 0 < 2)
    rw [hmul, hG]
    ring
  exact ⟨χ.ker, inferInstance, hNcard⟩

/-- Every group of order `2pq` is a semidirect product `N ⋊ ℤ/2` where `|N| = pq`. -/
theorem twoPQ_semidirect (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    [Finite G] (hG : Nat.card G = 2 * p * q) :
    ∃ (N : Subgroup G) (_ : N.Normal) (_ : Nat.card N = p * q)
      (K : Subgroup G) (φ : K →* MulAut N),
      Nonempty (G ≃* SemidirectProduct N K φ) := by
  obtain ⟨N, hNnormal, hNcard⟩ := twoPQ_normal_pq_subgroup p q hp hq h2p hpq hG
  haveI : N.Normal := hNnormal
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hp_coprime_two : Nat.Coprime p 2 := by
    refine (Nat.prime_two.coprime_iff_not_dvd.mpr ?_).symm
    intro h
    exact (Nat.not_even_iff_odd.mpr hpodd) ((even_iff_two_dvd).mpr h)
  have hq_coprime_two : Nat.Coprime q 2 := by
    refine (Nat.prime_two.coprime_iff_not_dvd.mpr ?_).symm
    intro h
    exact (Nat.not_even_iff_odd.mpr hqodd) ((even_iff_two_dvd).mpr h)
  have hcop : Nat.Coprime (p * q) 2 := hp_coprime_two.mul_left hq_coprime_two
  have hcard : Nat.card G = (p * q) * 2 := by
    rw [hG]
    ring
  obtain ⟨K, φ, hiso⟩ := schurZassenhaus_of_card hcard hcop N hNcard
  exact ⟨N, hNnormal, hNcard, K, φ, hiso⟩

/-! ### Exhaustiveness: `¬ p ∣ q - 1` case (4 classes) -/

/-- When `¬ p ∣ q - 1`, every group of order `2pq` is isomorphic to one of the four types. -/
theorem twoPQ_classification_4 (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (hmod : ¬ (p ∣ q - 1)) [Finite G] (hG : Nat.card G = 2 * p * q) :
    Nonempty (G ≃* twoPQ_I p q) ∨ Nonempty (G ≃* twoPQ_II p q) ∨
    Nonempty (G ≃* twoPQ_III p q) ∨ Nonempty (G ≃* twoPQ_IV p q) := sorry

/-! ### Exhaustiveness: `p ∣ q - 1` case (6 classes) -/

/-- When `p ∣ q - 1`, every group of order `2pq` is isomorphic to one of the six types.
    Requires a choice of primitive `p`-th root of unity `c₀` in `(ℤ/q)ˣ` and
    a unit `d₀` of order `2p` in `(ℤ/q)ˣ`. -/
theorem twoPQ_classification_6 [NeZero p] [NeZero (2 * p)]
    (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) (hmod : p ∣ q - 1)
    (c₀ : (ZMod q)ˣ) (hc₀ : c₀ ^ p = 1) (hc₀ne : c₀ ≠ 1)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1) (hd₀ord : orderOf d₀ = 2 * p)
    [Finite G] (hG : Nat.card G = 2 * p * q) :
    Nonempty (G ≃* twoPQ_I p q) ∨ Nonempty (G ≃* twoPQ_II p q) ∨
    Nonempty (G ≃* twoPQ_III p q) ∨ Nonempty (G ≃* twoPQ_IV p q) ∨
    Nonempty (G ≃* twoPQ_V p q c₀ hc₀) ∨ Nonempty (G ≃* twoPQ_VI p q d₀ hd₀) := sorry

/-! ### Commutativity / non-commutativity -/

theorem twoPQ_I_comm : ∀ a b : twoPQ_I p q, a * b = b * a := fun a b => mul_comm a b

theorem twoPQ_II_not_comm (h2p : 2 < p) (hpq : p < q) :
    ¬ ∀ a b : twoPQ_II p q, a * b = b * a := by
  have hpq_gt : 2 < p * q := by nlinarith
  intro hcomm
  haveI : NeZero (p * q) := ⟨by omega⟩
  have h := hcomm (DihedralGroup.r 1) (DihedralGroup.sr 0)
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h
  have h2 := DihedralGroup.sr.inj h
  have h3 : (-1 : ZMod (p * q)) = 1 := by
    have : (-1 : ZMod (p * q)) = 0 - 1 := by ring
    rw [this, h2]; ring
  have h4 : (2 : ZMod (p * q)) = 0 := by
    have h5 := sub_eq_zero.mpr h3
    rw [show (-1 : ZMod (p * q)) - 1 = -2 from by ring] at h5
    exact neg_eq_zero.mp h5
  rw [show (2 : ZMod (p * q)) = ((2 : ℕ) : ZMod (p * q)) from by push_cast; ring] at h4
  have h5 := (CharP.cast_eq_zero_iff (ZMod (p * q)) (p * q) 2).mp h4
  have h6 : p * q ≤ 2 := Nat.le_of_dvd (by norm_num) h5
  omega

theorem twoPQ_III_not_comm (h2p : 2 < p) :
    ¬ ∀ a b : twoPQ_III p q, a * b = b * a := by
  intro hcomm
  haveI : NeZero p := ⟨by omega⟩
  have h := hcomm (1, DihedralGroup.r 1) (1, DihedralGroup.sr 0)
  simp only [Prod.mk_mul_mk, mul_one] at h
  have h1 := congr_arg Prod.snd h
  simp only at h1
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h1
  have h2 := DihedralGroup.sr.inj h1
  have h3 : (-1 : ZMod p) = 1 := by
    have : (-1 : ZMod p) = 0 - 1 := by ring
    rw [this, h2]; ring
  have h4 : (2 : ZMod p) = 0 := by
    have h5 := sub_eq_zero.mpr h3
    rw [show (-1 : ZMod p) - 1 = -2 from by ring] at h5
    exact neg_eq_zero.mp h5
  rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by push_cast; ring] at h4
  have h5 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h4
  have h6 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h5
  omega

theorem twoPQ_IV_not_comm (h2p : 2 < p) (hpq : p < q) :
    ¬ ∀ a b : twoPQ_IV p q, a * b = b * a := by
  intro hcomm
  haveI : NeZero q := ⟨by omega⟩
  have h := hcomm (1, DihedralGroup.r 1) (1, DihedralGroup.sr 0)
  simp only [Prod.mk_mul_mk, mul_one] at h
  have h1 := congr_arg Prod.snd h
  simp only at h1
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h1
  have h2 := DihedralGroup.sr.inj h1
  have h3 : (-1 : ZMod q) = 1 := by
    have : (-1 : ZMod q) = 0 - 1 := by ring
    rw [this, h2]; ring
  have h4 : (2 : ZMod q) = 0 := by
    have h5 := sub_eq_zero.mpr h3
    rw [show (-1 : ZMod q) - 1 = -2 from by ring] at h5
    exact neg_eq_zero.mp h5
  rw [show (2 : ZMod q) = ((2 : ℕ) : ZMod q) from by push_cast; ring] at h4
  have h5 := (CharP.cast_eq_zero_iff (ZMod q) q 2).mp h4
  have h6 : q ≤ 2 := Nat.le_of_dvd (by norm_num) h5
  omega

theorem twoPQ_V_not_comm [NeZero p] (c : (ZMod q)ˣ) (hc : c ^ p = 1) (hcne : c ≠ 1)
    (hq : q.Prime) (h2p : 2 < p) :
    ¬ ∀ a b : twoPQ_V p q c hc, a * b = b * a := by
  intro hcomm
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  exact nonabRep_not_comm (by omega) c hc hcne
    (fun a b => by
      have h := hcomm (a, 1) (b, 1)
      simp only [Prod.mk_mul_mk, mul_one] at h
      exact congr_arg Prod.fst h)

theorem twoPQ_VI_not_comm [NeZero (2 * p)] (d : (ZMod q)ˣ) (hd : d ^ (2 * p) = 1) (hdne : d ≠ 1)
    (hq : q.Prime) :
    ¬ ∀ a b : twoPQ_VI p q d hd, a * b = b * a := by
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  exact nonabRep_not_comm (by have := NeZero.ne (2 * p); omega) d hd hdne

/-! ### Center cardinalities -/


theorem card_center_twoPQ_II (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) :
    Nat.card (center (twoPQ_II p q)) = 1 := by
  have hpq_odd : Odd (p * q) :=
    (hp.odd_of_ne_two (by omega)).mul (hq.odd_of_ne_two (by omega))
  have hpq_ne_one : p * q ≠ 1 := by nlinarith
  exact card_center_of_eq_bot (DihedralGroup.center_eq_bot_of_odd_ne_one hpq_odd hpq_ne_one)


theorem card_center_twoPQ_III (hp : p.Prime) (h2p : 2 < p) (hpq : p < q) :
    Nat.card (center (twoPQ_III p q)) = q := by
  rw [card_center_prod]
  rw [card_center_eq_card_of_comm _ (fun a b => mul_comm a b),
      card_center_of_eq_bot
        (DihedralGroup.center_eq_bot_of_odd_ne_one (hp.odd_of_ne_two (by omega)) hp.ne_one)]
  simp [card_cyclicRep (show q ≠ 0 by omega)]


theorem card_center_twoPQ_IV (hp : p.Prime) (hq : q.Prime)
    (h2p : 2 < p) (hpq : p < q) :
    Nat.card (center (twoPQ_IV p q)) = p := by
  rw [card_center_prod]
  rw [card_center_eq_card_of_comm _ (fun a b => mul_comm a b),
      card_center_of_eq_bot
        (DihedralGroup.center_eq_bot_of_odd_ne_one
          (hq.odd_of_ne_two (by omega)) hq.ne_one)]
  simp [card_cyclicRep hp.pos.ne']

/-! ### Distinctness

We use `PairwiseNonMulEquiv.of_center_card` with **center cardinality** as the invariant.
Since center cardinality is preserved by group isomorphisms, groups with different center sizes
are automatically non-isomorphic — no pairwise proof needed.

**4-class case** (¬ p ∣ q − 1): center sizes are `2pq, 1, q, p` — all distinct since `2 < p < q`,
so the invariant is injective and handles all 6 pairs with zero individual proofs.

**6-class case** (p ∣ q − 1): center sizes are `2pq, 1, q, p, 2, 1`. Only types II and VI share
center size 1, so the invariant handles 14 of 15 pairs; only II ≇ VI needs a separate argument. -/

def twoPQ_center_sizes_4 : Fin 4 → ℕ
  | 0 => 2 * p * q
  | 1 => 1
  | 2 => q
  | 3 => p

def twoPQ_center_sizes_6 : Fin 6 → ℕ
  | 0 => 2 * p * q
  | 1 => 1
  | 2 => q
  | 3 => p
  | 4 => 2
  | 5 => 1


theorem card_center_twoPQ_I (hp : p.Prime) (hq : q.Prime) :
    Nat.card (center (twoPQ_I p q)) = 2 * p * q := by
  rw [card_center_eq_card_of_comm _ (twoPQ_I_comm p q),
      card_twoPQ_I p q hp hq]

/-- **4-class distinctness via center cardinality.**
All four center sizes `2pq, 1, q, p` are distinct, so `of_center_card`
closes every pair. -/
theorem twoPQ_pairwiseDistinct_4 (hp : p.Prime) (hq : q.Prime)
    (h2p : 2 < p) (hpq : p < q) :
    PairwiseNonMulEquiv
      (rep4 (twoPQ_I p q) (twoPQ_II p q)
            (twoPQ_III p q) (twoPQ_IV p q)) := by
  apply PairwiseNonMulEquiv.of_center_card (twoPQ_center_sizes_4 p q)
  · intro k; fin_cases k
    · exact card_center_twoPQ_I p q hp hq
    · exact card_center_twoPQ_II p q hp hq h2p hpq
    · exact card_center_twoPQ_III p q hp h2p hpq
    · exact card_center_twoPQ_IV p q hp hq h2p hpq
  · intro i j heq _
    fin_cases i <;> fin_cases j <;>
      first | rfl | (dsimp [twoPQ_center_sizes_4] at heq; first | omega | nlinarith)

/-- Center of `NonabRep c hc` is trivial when the action is faithful.
    Requires `p` prime (so `ZMod p` is a field) and `orderOf c = q` (action is faithful). -/
theorem card_center_nonabRep [NeZero p] [NeZero q]
    (hp : p.Prime) (c : (ZMod p)ˣ) (hc : c ^ q = 1) (hcne : c ≠ 1)
    (hord : orderOf c = q) :
    Nat.card (center (NonabRep c hc)) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 < q := by
    have h1 : q ≠ 0 := NeZero.ne q
    have h2 : q ≠ 1 := by rw [← hord]; exact fun h => hcne (orderOf_eq_one_iff.mp h)
    omega
  haveI : Fact (1 < q) := ⟨hq1⟩
  apply card_center_of_eq_bot
  rw [eq_bot_iff]
  intro g hg
  simp only [Subgroup.mem_bot]
  rw [Subgroup.mem_center_iff] at hg
  -- For any central element g, both components must be 1
  -- Step 1: g.left is fixed by all actions → g.left = 1
  have hfixed : ∀ h, actionHom c hc h g.left = g.left := by
    intro h
    have key := congrArg SemidirectProduct.left (hg (SemidirectProduct.inr h))
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, one_mul, map_one, mul_one] at key
    exact key
  have hleft : g.left = 1 := by
    have h1 := hfixed (Multiplicative.ofAdd (1 : ZMod q))
    rw [show g.left = Multiplicative.ofAdd (Multiplicative.toAdd g.left) from
      (ofAdd_toAdd g.left).symm] at h1
    rw [actionHom_apply, ZMod.val_one, pow_one] at h1
    have h2 := Multiplicative.ofAdd.injective h1
    have hcsub : (↑c : ZMod p) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      intro heq; exact hcne (Units.val_injective (heq.trans Units.val_one.symm))
    have h3 : ((↑c : ZMod p) - 1) * Multiplicative.toAdd g.left = 0 := by
      rw [sub_mul, one_mul, sub_eq_zero]; exact h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hcsub
    · exact (ofAdd_toAdd g.left).symm.trans (congrArg Multiplicative.ofAdd h)
  -- Step 2: g.right acts trivially → g.right = 1
  have htriv : ∀ n, actionHom c hc g.right n = n := by
    intro n
    have key := congrArg SemidirectProduct.left (hg (SemidirectProduct.inl n))
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl] at key
    -- key : n * (actionHom c hc 1) g.left = g.left * (actionHom c hc g.right) n
    -- Simplify (actionHom c hc 1) g.left → g.left via map_one + identity
    have hmone : (actionHom c hc 1 : MulAut (Multiplicative (ZMod p))) g.left = g.left := by
      rw [map_one]; rfl
    rw [hmone, mul_comm n g.left] at key
    exact (mul_left_cancel key).symm
  have hright : g.right = 1 := by
    have h1 := htriv (Multiplicative.ofAdd (1 : ZMod p))
    rw [show g.right = Multiplicative.ofAdd (Multiplicative.toAdd g.right) from
      (ofAdd_toAdd g.right).symm] at h1
    rw [actionHom_apply, mul_one] at h1
    have h2 := Multiplicative.ofAdd.injective h1
    have h3 : c ^ (Multiplicative.toAdd g.right).val = 1 :=
      Units.val_injective (by rw [h2, Units.val_one])
    have h4 : q ∣ (Multiplicative.toAdd g.right).val := by
      have := orderOf_dvd_of_pow_eq_one h3; rwa [hord] at this
    have h5 : (Multiplicative.toAdd g.right).val < q := ZMod.val_lt _
    have h6 : (Multiplicative.toAdd g.right).val = 0 := by
      rcases Nat.eq_zero_or_pos (Multiplicative.toAdd g.right).val with h | h
      · exact h
      · exact absurd h5 (Nat.not_lt.mpr (Nat.le_of_dvd h h4))
    have h7 : Multiplicative.toAdd g.right = 0 := (ZMod.val_eq_zero _).mp h6
    exact (ofAdd_toAdd g.right).symm.trans (congrArg Multiplicative.ofAdd h7)
  exact SemidirectProduct.ext hleft hright

theorem card_center_twoPQ_V [NeZero p]
    (hp : p.Prime) (hq : q.Prime)
    (_h2p : 2 < p) (_hpq : p < q)
    (c₀ : (ZMod q)ˣ) (hc₀ : c₀ ^ p = 1) (hc₀ne : c₀ ≠ 1) :
    Nat.card (center (twoPQ_V p q c₀ hc₀)) = 2 := by
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hord : orderOf c₀ = p := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hc₀) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc₀ne
    · exact h
  change Nat.card (center (NonabRep c₀ hc₀ × Multiplicative (ZMod 2))) = 2
  rw [card_center_prod,
      card_center_nonabRep q p hq c₀ hc₀ hc₀ne hord,
      card_center_eq_card_of_comm _ (fun a b => mul_comm a b)]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem card_center_twoPQ_VI [NeZero (2 * p)]
    (hq : q.Prime) (_hpq : p < q)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1) (_hd₀ne : d₀ ≠ 1)
    (hd₀ord : orderOf d₀ = 2 * p) :
    Nat.card (center (twoPQ_VI p q d₀ hd₀)) = 1 := by
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hd₀ne' : d₀ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hd₀ord
    have := NeZero.ne (2 * p); omega
  exact card_center_nonabRep q (2 * p) hq d₀ hd₀ hd₀ne' hd₀ord

/-- **II ≇ VI**: both have trivial center, so we need a different
invariant (e.g. abelianization size or maximal cyclic-subgroup order).
-/
theorem twoPQ_II_not_VI [NeZero (2 * p)]
    (_hp : p.Prime) (_hq : q.Prime)
    (_h2p : 2 < p) (_hpq : p < q)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1) :
    ¬ Nonempty (twoPQ_II p q ≃* twoPQ_VI p q d₀ hd₀) := sorry

/-- **6-class distinctness via center cardinality.**
Center sizes `2pq, 1, q, p, 2, 1`: the invariant handles 14 of 15
pairs. Only the `(II, VI)` pair shares center size `1` and needs
`twoPQ_II_not_VI`. -/
theorem twoPQ_pairwiseDistinct_6 [NeZero p] [NeZero (2 * p)]
    (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (c₀ : (ZMod q)ˣ) (hc₀ : c₀ ^ p = 1) (hc₀ne : c₀ ≠ 1)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1)
    (hd₀ne : d₀ ≠ 1) (hd₀ord : orderOf d₀ = 2 * p) :
    PairwiseNonMulEquiv
      (rep6 (twoPQ_I p q) (twoPQ_II p q)
            (twoPQ_III p q) (twoPQ_IV p q)
            (twoPQ_V p q c₀ hc₀)
            (twoPQ_VI p q d₀ hd₀)) := by
  apply PairwiseNonMulEquiv.of_center_card (twoPQ_center_sizes_6 p q)
  · intro k; fin_cases k
    · exact card_center_twoPQ_I p q hp hq
    · exact card_center_twoPQ_II p q hp hq h2p hpq
    · exact card_center_twoPQ_III p q hp h2p hpq
    · exact card_center_twoPQ_IV p q hp hq h2p hpq
    · exact card_center_twoPQ_V p q hp hq h2p hpq c₀ hc₀ hc₀ne
    · exact card_center_twoPQ_VI p q hq hpq d₀ hd₀ hd₀ne hd₀ord
  · intro i j heq hiso
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | (unfold twoPQ_center_sizes_6 at heq; first | omega | nlinarith)
        | (dsimp [rep6] at hiso;
           exact absurd hiso (twoPQ_II_not_VI p q hp hq h2p hpq d₀ hd₀))
        | (dsimp [rep6] at hiso;
           exact absurd (hiso.map MulEquiv.symm)
             (twoPQ_II_not_VI p q hp hq h2p hpq d₀ hd₀))

/-! ### IsClassif bundles -/

/-- `IsClassif` bundle for the 4-class case (`¬ p ∣ q - 1`). -/
theorem twoPQ_isClassif_4 (hp : p.Prime) (hq : q.Prime)
    (h2p : 2 < p) (hpq : p < q) (hmod : ¬ (p ∣ q - 1)) :
    IsClassif (2 * p * q)
      (rep4 (twoPQ_I p q) (twoPQ_II p q)
            (twoPQ_III p q) (twoPQ_IV p q)) where
  card i := by
    fin_cases i
    · exact card_twoPQ_I p q hp hq
    · exact card_twoPQ_II p q hp hq
    · exact card_twoPQ_III p q hq
    · exact card_twoPQ_IV p q hp
  complete G _ hG := by
    haveI : Finite G := Nat.finite_of_card_ne_zero (hG ▸
      Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hp.ne_zero)
        hq.ne_zero)
    rcases twoPQ_classification_4 p q hp hq h2p hpq hmod hG
      with h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
  distinct := twoPQ_pairwiseDistinct_4 p q hp hq h2p hpq

/-- `IsClassif` bundle for the 6-class case (`p ∣ q - 1`). -/
theorem twoPQ_isClassif_6 [NeZero p] [NeZero (2 * p)]
    (hp : p.Prime) (hq : q.Prime)
    (h2p : 2 < p) (hpq : p < q) (hmod : p ∣ q - 1)
    (c₀ : (ZMod q)ˣ) (hc₀ : c₀ ^ p = 1) (hc₀ne : c₀ ≠ 1)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1)
    (hd₀ord : orderOf d₀ = 2 * p) (hd₀ne : d₀ ≠ 1) :
    IsClassif (2 * p * q)
      (rep6 (twoPQ_I p q) (twoPQ_II p q)
            (twoPQ_III p q) (twoPQ_IV p q)
            (twoPQ_V p q c₀ hc₀)
            (twoPQ_VI p q d₀ hd₀)) where
  card i := by
    fin_cases i
    · exact card_twoPQ_I p q hp hq
    · exact card_twoPQ_II p q hp hq
    · exact card_twoPQ_III p q hq
    · exact card_twoPQ_IV p q hp
    · exact card_twoPQ_V p q c₀ hc₀ hp hq
    · exact card_twoPQ_VI p q d₀ hd₀ hq
  complete G _ hG := by
    haveI : Finite G := Nat.finite_of_card_ne_zero (hG ▸
      Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hp.ne_zero)
        hq.ne_zero)
    rcases twoPQ_classification_6 p q hp hq h2p hpq hmod
        c₀ hc₀ hc₀ne d₀ hd₀ hd₀ord hG
      with h | h | h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩]
  distinct := twoPQ_pairwiseDistinct_6 p q hp hq h2p hpq
                c₀ hc₀ hc₀ne d₀ hd₀ hd₀ne hd₀ord

/-! ### Existence of required units -/

/-- When `p ∣ q - 1`, there exists a unit `c₀ : (ZMod q)ˣ` of order `p` with `c₀ ^ p = 1`. -/
theorem twoPQ_exists_unit_p (hp : p.Prime) (hq : q.Prime) (hmod : p ∣ q - 1) :
    ∃ (c₀ : (ZMod q)ˣ), orderOf c₀ = p ∧ c₀ ^ p = 1 ∧ c₀ ≠ 1 :=
  by
    obtain ⟨c₀, hc₀ord, hc₀pow⟩ := exists_unit_orderOf_eq (p := q) (q := p) hq hmod
    refine ⟨c₀, hc₀ord, hc₀pow, ?_⟩
    intro hc₀eq
    have horder : orderOf c₀ = 1 := by rw [hc₀eq, orderOf_one]
    have hpone : p = 1 := by rw [← hc₀ord, horder]
    exact hp.ne_one hpone

/-- When `p ∣ q - 1`, there exists a unit `d₀ : (ZMod q)ˣ` of order `2p` with
    `d₀ ^ (2 * p) = 1`. (Since `q` is odd, `2 ∣ q - 1`, and `gcd(2, p) = 1` gives
    `2p ∣ q - 1`.) -/
theorem twoPQ_exists_unit_2p (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hmod : p ∣ q - 1) :
    ∃ (d₀ : (ZMod q)ˣ), orderOf d₀ = 2 * p ∧ d₀ ^ (2 * p) = 1 :=
  by
    have hpne2 : p ≠ 2 := by omega
    have hpodd : Odd p := hp.odd_of_ne_two hpne2
    have hnot_two_dvd_p : ¬ 2 ∣ p := by
      intro h
      exact (Nat.not_even_iff_odd.mpr hpodd) ((even_iff_two_dvd).mpr h)
    have hcop : Nat.Coprime 2 p := Nat.prime_two.coprime_iff_not_dvd.mpr hnot_two_dvd_p
    have hqne2 : q ≠ 2 := by
      intro hqeq
      have hp_dvd_one : p ∣ 1 := by simpa [hqeq] using hmod
      have hple : p ≤ 1 := Nat.le_of_dvd (by norm_num) hp_dvd_one
      omega
    have hqodd : Odd q := hq.odd_of_ne_two hqne2
    have htwo_dvd_qsub : 2 ∣ q - 1 := by
      obtain ⟨k, hk⟩ := hqodd
      refine ⟨k, ?_⟩
      omega
    have htwop_dvd : 2 * p ∣ q - 1 :=
      hcop.mul_dvd_of_dvd_of_dvd htwo_dvd_qsub hmod
    exact exists_unit_orderOf_eq (p := q) (q := 2 * p) hq htwop_dvd

end Smallgroups.UsefulTheorems
