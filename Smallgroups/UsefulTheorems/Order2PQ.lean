/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Smallgroups.UsefulTheorems.PrimePairDihedral
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Smallgroups.UsefulTheorems.Counting
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

/-! ### Distinctness -/

theorem twoPQ_I_not_II (_hp : p.Prime) (_hq : q.Prime) (h2p : 2 < p) (hpq : p < q) :
    ¬ Nonempty (twoPQ_I p q ≃* twoPQ_II p q) := by
  have hpq_ne_one : p * q ≠ 1 := by
    nlinarith [h2p, hpq]
  change ¬ Nonempty (CyclicRep (2 * p * q) ≃* DihedralGroup (p * q))
  rw [Nat.mul_assoc]
  exact cyclicRep_not_mulEquiv_dihedral (p := p * q) hpq_ne_one

theorem twoPQ_I_not_III (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) :
    ¬ Nonempty (twoPQ_I p q ≃* twoPQ_III p q) := sorry

theorem twoPQ_I_not_IV (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) :
    ¬ Nonempty (twoPQ_I p q ≃* twoPQ_IV p q) := sorry

theorem twoPQ_II_not_III (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) :
    ¬ Nonempty (twoPQ_II p q ≃* twoPQ_III p q) := sorry

theorem twoPQ_II_not_IV (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) :
    ¬ Nonempty (twoPQ_II p q ≃* twoPQ_IV p q) := sorry

theorem twoPQ_III_not_IV (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) :
    ¬ Nonempty (twoPQ_III p q ≃* twoPQ_IV p q) := sorry

theorem twoPQ_I_not_V [NeZero p] (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (c₀ : (ZMod q)ˣ) (hc₀ : c₀ ^ p = 1) (hc₀ne : c₀ ≠ 1) :
    ¬ Nonempty (twoPQ_I p q ≃* twoPQ_V p q c₀ hc₀) := sorry

theorem twoPQ_I_not_VI [NeZero (2 * p)] (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1) :
    ¬ Nonempty (twoPQ_I p q ≃* twoPQ_VI p q d₀ hd₀) := sorry

theorem twoPQ_II_not_V [NeZero p] (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (c₀ : (ZMod q)ˣ) (hc₀ : c₀ ^ p = 1) (hc₀ne : c₀ ≠ 1) :
    ¬ Nonempty (twoPQ_II p q ≃* twoPQ_V p q c₀ hc₀) := sorry

theorem twoPQ_II_not_VI [NeZero (2 * p)] (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1) :
    ¬ Nonempty (twoPQ_II p q ≃* twoPQ_VI p q d₀ hd₀) := sorry

theorem twoPQ_III_not_V [NeZero p] (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (c₀ : (ZMod q)ˣ) (hc₀ : c₀ ^ p = 1) (hc₀ne : c₀ ≠ 1) :
    ¬ Nonempty (twoPQ_III p q ≃* twoPQ_V p q c₀ hc₀) := sorry

theorem twoPQ_III_not_VI [NeZero (2 * p)] (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1) :
    ¬ Nonempty (twoPQ_III p q ≃* twoPQ_VI p q d₀ hd₀) := sorry

theorem twoPQ_IV_not_V [NeZero p] (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (c₀ : (ZMod q)ˣ) (hc₀ : c₀ ^ p = 1) (hc₀ne : c₀ ≠ 1) :
    ¬ Nonempty (twoPQ_IV p q ≃* twoPQ_V p q c₀ hc₀) := sorry

theorem twoPQ_IV_not_VI [NeZero (2 * p)] (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1) :
    ¬ Nonempty (twoPQ_IV p q ≃* twoPQ_VI p q d₀ hd₀) := sorry

theorem twoPQ_V_not_VI [NeZero p] [NeZero (2 * p)]
    (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (c₀ : (ZMod q)ˣ) (hc₀ : c₀ ^ p = 1) (hc₀ne : c₀ ≠ 1)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1) (hd₀ord : orderOf d₀ = 2 * p) :
    ¬ Nonempty (twoPQ_V p q c₀ hc₀ ≃* twoPQ_VI p q d₀ hd₀) := sorry

/-! ### IsClassif bundles -/

/-- `IsClassif` bundle for the 4-class case (`¬ p ∣ q - 1`). -/
theorem twoPQ_isClassif_4 (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (hmod : ¬ (p ∣ q - 1)) :
    IsClassif (2 * p * q) (rep4 (twoPQ_I p q) (twoPQ_II p q) (twoPQ_III p q) (twoPQ_IV p q)) :=
  isClassif_four _ _ _ _
    (card_twoPQ_I p q hp hq) (card_twoPQ_II p q hp hq) (card_twoPQ_III p q hq)
    (card_twoPQ_IV p q hp)
    (fun G _ hG => by
      haveI : Finite G := Nat.finite_of_card_ne_zero
        (hG ▸ Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hp.ne_zero) hq.ne_zero)
      exact twoPQ_classification_4 p q hp hq h2p hpq hmod hG)
    (twoPQ_I_not_II p q hp hq h2p hpq) (twoPQ_I_not_III p q hp hq h2p hpq)
    (twoPQ_I_not_IV p q hp hq h2p hpq) (twoPQ_II_not_III p q hp hq h2p hpq)
    (twoPQ_II_not_IV p q hp hq h2p hpq) (twoPQ_III_not_IV p q hp hq h2p hpq)

/-- `IsClassif` bundle for the 6-class case (`p ∣ q - 1`). -/
theorem twoPQ_isClassif_6 [NeZero p] [NeZero (2 * p)]
    (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) (hmod : p ∣ q - 1)
    (c₀ : (ZMod q)ˣ) (hc₀ : c₀ ^ p = 1) (hc₀ne : c₀ ≠ 1)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1) (hd₀ord : orderOf d₀ = 2 * p) :
    IsClassif (2 * p * q) (rep6 (twoPQ_I p q) (twoPQ_II p q) (twoPQ_III p q) (twoPQ_IV p q)
      (twoPQ_V p q c₀ hc₀) (twoPQ_VI p q d₀ hd₀)) := sorry

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
