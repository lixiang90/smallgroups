/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Smallgroups.UsefulTheorems.PrimePairDihedral
import Smallgroups.UsefulTheorems.PrimePairCyclic
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

/-! ### Exhaustiveness helpers -/

/-- Generalized `nonempty_mulEquiv_dihedral` for odd (not necessarily prime) modulus. -/
private theorem nonempty_mulEquiv_dihedral_odd {G : Type*} [Group G] {n : ℕ}
    (hn : n ≠ 0) (hodd : Odd n) [Finite G]
    (a b : G) (han : orderOf a = n) (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (hcard : Nat.card G = 2 * n) :
    Nonempty (G ≃* DihedralGroup n) := by
  haveI : NeZero n := ⟨hn⟩
  haveI : Fintype G := Fintype.ofFinite G
  have han1 : a ^ n = 1 := by rw [← han]; exact pow_orderOf_eq_one a
  have hc_add : ∀ i j : ZMod n, a ^ (i + j).val = a ^ i.val * a ^ j.val := by
    intro i j; rw [← pow_add]; apply pow_eq_pow_iff_modEq.mpr
    rw [han, ZMod.val_add]; exact Nat.mod_modEq _ _
  have hc_sub : ∀ i j : ZMod n, a ^ (j - i).val = a ^ j.val * (a ^ i.val)⁻¹ := by
    intro i j; have h := hc_add (j - i) i
    rw [sub_add_cancel] at h; exact eq_mul_inv_iff_mul_eq.mpr h.symm
  have hab : a * b = b * a⁻¹ := by
    have h2 : b * a = a⁻¹ * b := by rw [← hba]; group
    have h : a * b * a = b := by
      calc a * b * a = a * (b * a) := by group
        _ = a * (a⁻¹ * b) := by rw [h2]
        _ = b := by group
    calc a * b = a * b * a * a⁻¹ := by group
      _ = b * a⁻¹ := by rw [h]
  have hak : ∀ k : ℕ, a ^ k * b = b * (a⁻¹) ^ k := by
    intro k; induction k with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_assoc, hab, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have hcom : ∀ m₀ n₀ : ℕ, (a ^ m₀)⁻¹ * a ^ n₀ = a ^ n₀ * (a ^ m₀)⁻¹ := fun m₀ n₀ =>
    ((((Commute.refl a).pow_pow n₀ m₀).inv_right).eq).symm
  have hrsr : ∀ m₀ n₀ : ℕ, a ^ m₀ * (b * a ^ n₀) = b * (a ^ n₀ * (a ^ m₀)⁻¹) := by
    intro m₀ n₀; rw [← mul_assoc, hak, mul_assoc, inv_pow, hcom]
  have hsrsr : ∀ m₀ n₀ : ℕ, b * a ^ m₀ * (b * a ^ n₀) = a ^ n₀ * (a ^ m₀)⁻¹ := by
    intro m₀ n₀; rw [mul_assoc, hrsr, ← mul_assoc, ← pow_two, hb2, one_mul]
  let φ : DihedralGroup n → G := fun x => match x with
    | .r i => a ^ i.val
    | .sr i => b * a ^ i.val
  have hφmul : ∀ x y, φ (x * y) = φ x * φ y := by
    rintro (i | i) (j | j)
    · exact hc_add i j
    · change b * a ^ (j - i).val = a ^ i.val * (b * a ^ j.val)
      rw [hc_sub, hrsr]
    · change b * a ^ (i + j).val = b * a ^ i.val * a ^ j.val
      rw [hc_add, mul_assoc]
    · change a ^ (j - i).val = b * a ^ i.val * (b * a ^ j.val)
      rw [hc_sub, hsrsr]
  let f : DihedralGroup n →* G := MonoidHom.mk' φ hφmul
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro (i | i) hx
    · have hx' : a ^ i.val = 1 := hx
      have hdvd : orderOf a ∣ i.val := orderOf_dvd_of_pow_eq_one hx'
      rw [han] at hdvd
      have hi0 : i = 0 := by
        rw [← ZMod.val_eq_zero]
        exact Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt i)
      rw [hi0]; exact DihedralGroup.one_def.symm
    · exfalso
      have hsr : b * a ^ i.val = 1 := hx
      have hbeq : b = (a ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left hsr
      have hbpow : b ^ n = 1 := by
        rw [hbeq, inv_pow, ← pow_mul, mul_comm i.val n, pow_mul, han1, one_pow, inv_one]
      have h2_dvd_n : 2 ∣ n :=
        (orderOf_eq_prime hb2 hb1) ▸ orderOf_dvd_of_pow_eq_one hbpow
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2_dvd_n)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by rw [DihedralGroup.card, ← Nat.card_eq_fintype_card, hcard]⟩
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

/-- Product-dihedral: from elements `c` (order `n`), `d` (order `m`), `b` (involution) where
`b` inverts `c`, commutes with `d`, and `c`, `d` commute, with coprime orders, deduce
`G ≅ ℤ/m × D_n`. -/
private theorem nonempty_mulEquiv_prod_dihedral {G : Type*} [Group G]
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (_hm_odd : Odd m) (_hn_odd : Odd n)
    (_hcop : Nat.Coprime m n) [Finite G]
    (c d b : G) (_hc_ord : orderOf c = n) (_hd_ord : orderOf d = m)
    (_hb1 : b ≠ 1) (_hb2 : b ^ 2 = 1)
    (_hba : b * c * b⁻¹ = c⁻¹) (_hbd : b * d = d * b)
    (_hcd : c * d = d * c)
    (_hcard : Nat.card G = 2 * m * n) :
    Nonempty (G ≃* Multiplicative (ZMod m) × DihedralGroup n) := by
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero n := ⟨hn⟩
  haveI : Fintype G := Fintype.ofFinite G
  have hdc : Commute d c := _hcd.symm
  have hdb : Commute d b := _hbd.symm
  have hd_m1 : d ^ m = 1 := by rw [← _hd_ord]; exact pow_orderOf_eq_one d
  -- Dihedral machinery for `c, b` (mirrors `nonempty_mulEquiv_dihedral_odd`)
  have hc_add : ∀ i j : ZMod n, c ^ (i + j).val = c ^ i.val * c ^ j.val := by
    intro i j; rw [← pow_add]; apply pow_eq_pow_iff_modEq.mpr
    rw [_hc_ord, ZMod.val_add]; exact Nat.mod_modEq _ _
  have hc_sub : ∀ i j : ZMod n, c ^ (j - i).val = c ^ j.val * (c ^ i.val)⁻¹ := by
    intro i j; have h := hc_add (j - i) i
    rw [sub_add_cancel] at h; exact eq_mul_inv_iff_mul_eq.mpr h.symm
  have hcb : c * b = b * c⁻¹ := by
    have h2 : b * c = c⁻¹ * b := by rw [← _hba]; group
    have h : c * b * c = b := by
      calc c * b * c = c * (b * c) := by group
        _ = c * (c⁻¹ * b) := by rw [h2]
        _ = b := by group
    calc c * b = c * b * c * c⁻¹ := by group
      _ = b * c⁻¹ := by rw [h]
  have hck : ∀ k : ℕ, c ^ k * b = b * (c⁻¹) ^ k := by
    intro k; induction k with
    | zero => simp
    | succ mm ih => rw [pow_succ, mul_assoc, hcb, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have hcom : ∀ m₀ n₀ : ℕ, (c ^ m₀)⁻¹ * c ^ n₀ = c ^ n₀ * (c ^ m₀)⁻¹ := fun m₀ n₀ =>
    ((((Commute.refl c).pow_pow n₀ m₀).inv_right).eq).symm
  have hrsr : ∀ m₀ n₀ : ℕ, c ^ m₀ * (b * c ^ n₀) = b * (c ^ n₀ * (c ^ m₀)⁻¹) := by
    intro m₀ n₀; rw [← mul_assoc, hck, mul_assoc, inv_pow, hcom]
  have hsrsr : ∀ m₀ n₀ : ℕ, b * c ^ m₀ * (b * c ^ n₀) = c ^ n₀ * (c ^ m₀)⁻¹ := by
    intro m₀ n₀; rw [mul_assoc, hrsr, ← mul_assoc, ← pow_two, _hb2, one_mul]
  -- The dihedral part as a function
  let ψ : DihedralGroup n → G := fun x => match x with
    | .r i => c ^ i.val
    | .sr i => b * c ^ i.val
  have hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    rintro (i | i) (j | j)
    · exact hc_add i j
    · change b * c ^ (j - i).val = c ^ i.val * (b * c ^ j.val)
      rw [hc_sub, hrsr]
    · change b * c ^ (i + j).val = b * c ^ i.val * c ^ j.val
      rw [hc_add, mul_assoc]
    · change c ^ (j - i).val = b * c ^ i.val * (b * c ^ j.val)
      rw [hc_sub, hsrsr]
  -- The cyclic part addition law
  have hd_add : ∀ i j : ZMod m, d ^ (i + j).val = d ^ i.val * d ^ j.val := by
    intro i j; rw [← pow_add]; apply pow_eq_pow_iff_modEq.mpr
    rw [_hd_ord, ZMod.val_add]; exact Nat.mod_modEq _ _
  -- Powers of `d` commute with the entire dihedral part
  have hd_comm : ∀ (a : ℕ) (y : DihedralGroup n), Commute (d ^ a) (ψ y) := by
    intro a y
    cases y with
    | r i => exact hdc.pow_pow a i.val
    | sr i =>
        change Commute (d ^ a) (b * c ^ i.val)
        exact (hdb.pow_left a).mul_right (hdc.pow_pow a i.val)
  -- The combined map
  let Φ : Multiplicative (ZMod m) × DihedralGroup n → G := fun z =>
    d ^ (Multiplicative.toAdd z.1).val * ψ z.2
  have hΦmul : ∀ z w, Φ (z * w) = Φ z * Φ w := by
    rintro ⟨x1, y1⟩ ⟨x2, y2⟩
    change d ^ (Multiplicative.toAdd (x1 * x2)).val * ψ (y1 * y2)
        = (d ^ (Multiplicative.toAdd x1).val * ψ y1)
          * (d ^ (Multiplicative.toAdd x2).val * ψ y2)
    rw [hψmul y1 y2,
        show Multiplicative.toAdd (x1 * x2)
            = Multiplicative.toAdd x1 + Multiplicative.toAdd x2 from rfl,
        hd_add]
    have hBP := (hd_comm (Multiplicative.toAdd x2).val y1).eq
    rw [mul_assoc (d ^ (Multiplicative.toAdd x1).val) (d ^ (Multiplicative.toAdd x2).val)
          (ψ y1 * ψ y2),
        ← mul_assoc (d ^ (Multiplicative.toAdd x2).val) (ψ y1) (ψ y2),
        hBP,
        mul_assoc (ψ y1) (d ^ (Multiplicative.toAdd x2).val) (ψ y2),
        ← mul_assoc (d ^ (Multiplicative.toAdd x1).val) (ψ y1)
          (d ^ (Multiplicative.toAdd x2).val * ψ y2)]
  let f : Multiplicative (ZMod m) × DihedralGroup n →* G := MonoidHom.mk' Φ hΦmul
  -- Coprime orders ⇒ the cyclic subgroups intersect trivially
  have key2 : ∀ (s t : ℕ), d ^ s * c ^ t = 1 → d ^ s = 1 ∧ c ^ t = 1 := by
    intro s t h
    have e1 : d ^ s = (c ^ t)⁻¹ := mul_eq_one_iff_eq_inv.mp h
    have e2 : c ^ (t * m) = 1 := by
      have hh : (d ^ s) ^ m = ((c ^ t)⁻¹) ^ m := by rw [e1]
      rw [← pow_mul, mul_comm s m, pow_mul, hd_m1, one_pow] at hh
      rw [inv_pow, ← pow_mul] at hh
      rw [eq_comm, inv_eq_one] at hh
      exact hh
    have hndvd : n ∣ t := by
      have hdvd : orderOf c ∣ t * m := orderOf_dvd_of_pow_eq_one e2
      rw [_hc_ord] at hdvd
      exact (_hcop.symm).dvd_of_dvd_mul_right hdvd
    have hct1 : c ^ t = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [_hc_ord]; exact hndvd)
    refine ⟨?_, hct1⟩
    rw [hct1, mul_one] at h; exact h
  -- Injectivity of `f`
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, (i | i)⟩ hx
    · have hx' : d ^ (Multiplicative.toAdd x).val * c ^ i.val = 1 := hx
      obtain ⟨hd1, hc1⟩ := key2 (Multiplicative.toAdd x).val i.val hx'
      have hi0 : i = 0 := by
        rw [← ZMod.val_eq_zero]
        have hdvd : orderOf c ∣ i.val := orderOf_dvd_of_pow_eq_one hc1
        rw [_hc_ord] at hdvd
        exact Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt i)
      have hx1 : x = 1 := by
        have hdvd : orderOf d ∣ (Multiplicative.toAdd x).val := orderOf_dvd_of_pow_eq_one hd1
        rw [_hd_ord] at hdvd
        have hval0 : (Multiplicative.toAdd x).val = 0 :=
          Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
        have htoadd0 : Multiplicative.toAdd x = 0 := (ZMod.val_eq_zero _).mp hval0
        rw [← ofAdd_toAdd x, htoadd0, ofAdd_zero]
      rw [hx1, hi0]; rfl
    · exfalso
      have hx' : d ^ (Multiplicative.toAdd x).val * (b * c ^ i.val) = 1 := hx
      set a := (Multiplicative.toAdd x).val
      set t := i.val
      have huv : Commute (d ^ a) (c ^ t) := hdc.pow_pow a t
      have step1 : b * c ^ t = (d ^ a)⁻¹ := eq_inv_of_mul_eq_one_right hx'
      have hbeq : b = (d ^ a)⁻¹ * (c ^ t)⁻¹ := by rw [← step1]; group
      have hbeq2 : b = (d ^ a * c ^ t)⁻¹ := by
        rw [hbeq, mul_inv_rev]; exact (huv.inv_left.inv_right).eq
      have hw2 : (d ^ a * c ^ t) ^ 2 = 1 := by
        have hh : b ^ 2 = ((d ^ a * c ^ t)⁻¹) ^ 2 := by rw [hbeq2]
        rw [_hb2, inv_pow] at hh
        rw [eq_comm, inv_eq_one] at hh
        exact hh
      have hexp : (d ^ a * c ^ t) ^ 2 = d ^ (2 * a) * c ^ (2 * t) := by
        rw [huv.mul_pow, ← pow_mul, ← pow_mul, mul_comm a 2, mul_comm t 2]
      have hb2eq : d ^ (2 * a) * c ^ (2 * t) = 1 := by rw [← hexp]; exact hw2
      obtain ⟨hd2, hc2⟩ := key2 (2 * a) (2 * t) hb2eq
      have hda : d ^ a = 1 := by
        have hdvd : orderOf d ∣ 2 * a := orderOf_dvd_of_pow_eq_one hd2
        rw [_hd_ord] at hdvd
        have hma : m ∣ a := (Nat.coprime_two_right.mpr _hm_odd).dvd_of_dvd_mul_left hdvd
        exact orderOf_dvd_iff_pow_eq_one.mp (by rw [_hd_ord]; exact hma)
      have hct : c ^ t = 1 := by
        have hdvd : orderOf c ∣ 2 * t := orderOf_dvd_of_pow_eq_one hc2
        rw [_hc_ord] at hdvd
        have hnt : n ∣ t := (Nat.coprime_two_right.mpr _hn_odd).dvd_of_dvd_mul_left hdvd
        exact orderOf_dvd_iff_pow_eq_one.mp (by rw [_hc_ord]; exact hnt)
      have hb1' : b = 1 := by rw [hbeq, hda, hct, inv_one, mul_one]
      exact _hb1 hb1'
  -- Cardinality count
  have hMcard : Fintype.card (Multiplicative (ZMod m)) = m :=
    (Fintype.card_congr Multiplicative.toAdd).trans (ZMod.card m)
  have hcard_eq :
      Fintype.card (Multiplicative (ZMod m) × DihedralGroup n) = Fintype.card G := by
    rw [Fintype.card_prod, hMcard, DihedralGroup.card, ← Nat.card_eq_fintype_card, _hcard]
    ring
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard_eq⟩
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

/-! ### Exhaustiveness: `¬ p ∣ q - 1` case (4 classes) -/

/-- When `¬ p ∣ q - 1`, every group of order `2pq` is isomorphic to one of the four types. -/
theorem twoPQ_classification_4 (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    (hmod : ¬ (p ∣ q - 1)) [Finite G] (hG : Nat.card G = 2 * p * q) :
    Nonempty (G ≃* twoPQ_I p q) ∨ Nonempty (G ≃* twoPQ_II p q) ∨
    Nonempty (G ≃* twoPQ_III p q) ∨ Nonempty (G ≃* twoPQ_IV p q) := by
  haveI : Fintype G := Fintype.ofFinite G
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  -- Step 1: get normal subgroup N of order pq
  obtain ⟨N, hNnorm, hNcard⟩ := twoPQ_normal_pq_subgroup p q hp hq h2p hpq hG
  haveI : N.Normal := hNnorm
  -- Step 2: N is cyclic (since |N| = pq with q > p and ¬ p ∣ q - 1)
  haveI : IsCyclic ↥N :=
    isCyclic_of_card_eq_prime_mul hq hp hpq hmod
      (show Nat.card ↥N = q * p by rw [hNcard, mul_comm])
  -- Step 3: get generator a of N with orderOf a = pq
  obtain ⟨a₀, ha₀⟩ := IsCyclic.exists_monoid_generator (α := ↥N)
  have ha₀_ord : orderOf a₀ = p * q :=
    (orderOf_eq_card_of_forall_mem_powers ha₀).trans hNcard
  set a := (a₀ : G) with ha_def
  have ha_ord : orderOf a = p * q := by
    change orderOf (a₀ : G) = p * q
    rw [show (a₀ : G) = N.subtype a₀ from rfl,
      orderOf_injective N.subtype N.subtype_injective, ha₀_ord]
  have ha_mem : a ∈ N := a₀.property
  -- Step 4: get involution b with orderOf b = 2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := G) 2
    ⟨p * q, by rw [hG]; ring⟩
  have hb1 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; exact absurd hb (by norm_num)
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  -- Step 5: zpowers a = N
  have hA_eq_N : zpowers a = N := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx; obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      exact N.zpow_mem ha_mem k
    · have : Nat.card ↥(zpowers a) = p * q := by rw [Nat.card_zpowers, ha_ord]
      omega
  -- Step 6: conjugation b * a * b⁻¹ = a ^ k
  have hconj_mem : b * a * b⁻¹ ∈ zpowers a := by
    rw [hA_eq_N]; exact hNnorm.conj_mem a ha_mem b
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hconj_mem
  -- Step 7: k² ≡ 1 (mod pq)
  have hbb : b * b = 1 := by rw [← pow_two]; exact hb2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hconj2 : b * (b * a * b⁻¹) * b⁻¹ = a := by
    rw [hbinv]
    calc b * (b * a * b) * b = (b * b) * a * (b * b) := by group
      _ = a := by rw [hbb, one_mul, mul_one]
  have hkk : a ^ (k * k) = a := by rw [zpow_mul, hk, conj_zpow, hk, hconj2]
  have hk1 : a ^ (k * k - 1) = 1 := by
    rw [zpow_sub, hkk, zpow_one]; exact mul_inv_cancel a
  have hpqd : (↑(p * q) : ℤ) ∣ (k - 1) * (k + 1) := by
    have h0 : (k * k - 1) ≡ 0 [ZMOD orderOf a] := zpow_eq_one_iff_modEq.mp hk1
    rw [ha_ord, Int.modEq_zero_iff_dvd] at h0
    rwa [show (k - 1) * (k + 1) = k * k - 1 by ring]
  -- Step 8: split by p and q
  have hpd : (↑p : ℤ) ∣ (k - 1) * (k + 1) :=
    dvd_trans (by exact_mod_cast dvd_mul_right p q) hpqd
  have hqd : (↑q : ℤ) ∣ (k - 1) * (k + 1) :=
    dvd_trans (by exact_mod_cast dvd_mul_left q p) hpqd
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hpd with hp_k1 | hp_k1
  <;> rcases (Nat.prime_iff_prime_int.mp hq).dvd_or_dvd hqd with hq_k1 | hq_k1
  · -- Case I: p ∣ k-1 and q ∣ k-1 → k ≡ 1 (mod pq) → abelian → cyclic
    left
    have hpq_k1 : (↑(p * q) : ℤ) ∣ k - 1 := by
      rw [Nat.cast_mul]
      exact IsCoprime.mul_dvd
        (by exact_mod_cast (Nat.coprime_primes hp hq).mpr (by omega)) hp_k1 hq_k1
    have hak1 : a ^ k = a := by
      have : a ^ (k - 1) = 1 := by
        rw [zpow_eq_one_iff_modEq, ha_ord, Int.modEq_zero_iff_dvd]; exact hpq_k1
      rw [zpow_sub, zpow_one] at this; exact mul_inv_eq_one.mp this
    have hba1 : b * a * b⁻¹ = a := by rw [← hk, hak1]
    have hcomm : Commute a b := by
      have : b * a = a * b :=
        calc b * a = b * a * b⁻¹ * b := by group
          _ = a * b := by rw [hba1]
      exact this.symm
    have hcop : (orderOf a).Coprime (orderOf b) := by
      rw [ha_ord, hb]
      exact Nat.coprime_two_right.mpr (hpodd.mul hqodd)
    haveI : IsCyclic G := by
      have hord : orderOf (a * b) = 2 * p * q := by
        rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, ha_ord, hb]; ring
      exact isCyclic_of_orderOf_eq_card (a * b) (by rw [hord, hG])
    exact cyclicRep_classification
      (Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hp.pos.ne') hq.pos.ne') hG
  · -- Case IV: p ∣ k-1 and q ∣ k+1 → ℤ/p × D_q
    right; right; right
    set c := a ^ (q : ℕ) with hc_def
    set d := a ^ (p : ℕ) with hd_def
    have hc_ord : orderOf c = p := by
      rw [hc_def, orderOf_pow' a hq.ne_zero, ha_ord,
        Nat.gcd_eq_right (dvd_mul_left q p), Nat.mul_div_cancel p hq.pos]
    have hd_ord : orderOf d = q := by
      rw [hd_def, orderOf_pow' a hp.ne_zero, ha_ord,
        Nat.gcd_eq_right (dvd_mul_right p q), Nat.mul_div_cancel_left q hp.pos]
    -- b commutes with c = a^q (since p | k-1)
    have hbc_comm : b * c = c * b := by
      have h1 : b * c * b⁻¹ = a ^ (k * ↑q) := by
        calc b * c * b⁻¹ = (b * a * b⁻¹) ^ (q : ℕ) := by rw [hc_def]; exact conj_pow.symm
          _ = (a ^ k) ^ (q : ℕ) := by rw [hk]
          _ = a ^ (k * ↑q) := by rw [← zpow_natCast (a ^ k), ← zpow_mul]
      have h2 : a ^ (k * ↑q) = c := by
        rw [hc_def, ← zpow_natCast, zpow_eq_zpow_iff_modEq, ha_ord,
          Int.modEq_iff_dvd, show (↑q : ℤ) - k * ↑q = -(↑q * (k - 1)) from by ring,
          dvd_neg, Nat.cast_mul, show (↑p : ℤ) * ↑q = ↑q * ↑p from mul_comm _ _]
        exact mul_dvd_mul_left ↑q hp_k1
      calc b * c = b * c * b⁻¹ * b := by group
        _ = c * b := by rw [h1, h2]
    -- b inverts d = a^p (since q | k+1)
    have hbd_inv : b * d * b⁻¹ = d⁻¹ := by
      have h1 : b * d * b⁻¹ = a ^ (k * ↑p) := by
        calc b * d * b⁻¹ = (b * a * b⁻¹) ^ (p : ℕ) := by rw [hd_def]; exact conj_pow.symm
          _ = (a ^ k) ^ (p : ℕ) := by rw [hk]
          _ = a ^ (k * ↑p) := by rw [← zpow_natCast (a ^ k), ← zpow_mul]
      have h2 : a ^ (k * ↑p) = a ^ (-(↑p : ℤ)) := by
        rw [zpow_eq_zpow_iff_modEq, ha_ord, Int.modEq_iff_dvd,
          show -(↑p : ℤ) - k * ↑p = -(↑p * (k + 1)) from by ring, dvd_neg,
          Nat.cast_mul]
        exact mul_dvd_mul_left ↑p hq_k1
      rw [h1, h2, zpow_neg, zpow_natCast]
    -- d and c commute (powers of a)
    have hdc_comm : d * c = c * d := by
      rw [hd_def, hc_def]; exact (Commute.refl a).pow_pow p q
    -- Apply helper: inverted = d (order q), commuting = c (order p)
    exact nonempty_mulEquiv_prod_dihedral hp.ne_zero hq.ne_zero hpodd hqodd
      ((Nat.coprime_primes hp hq).mpr (by omega))
      d c b hd_ord hc_ord hb1 hb2 hbd_inv hbc_comm hdc_comm
      (show Nat.card G = 2 * p * q from hG)
  · -- Case III: p ∣ k+1 and q ∣ k-1 → ℤ/q × D_p
    right; right; left
    set c := a ^ (q : ℕ) with hc_def
    set d := a ^ (p : ℕ) with hd_def
    have hc_ord : orderOf c = p := by
      rw [hc_def, orderOf_pow' a hq.ne_zero, ha_ord,
        Nat.gcd_eq_right (dvd_mul_left q p), Nat.mul_div_cancel p hq.pos]
    have hd_ord : orderOf d = q := by
      rw [hd_def, orderOf_pow' a hp.ne_zero, ha_ord,
        Nat.gcd_eq_right (dvd_mul_right p q), Nat.mul_div_cancel_left q hp.pos]
    -- b inverts c = a^q (since p | k+1)
    have hbc_inv : b * c * b⁻¹ = c⁻¹ := by
      have h1 : b * c * b⁻¹ = a ^ (k * ↑q) := by
        calc b * c * b⁻¹ = (b * a * b⁻¹) ^ (q : ℕ) := by rw [hc_def]; exact conj_pow.symm
          _ = (a ^ k) ^ (q : ℕ) := by rw [hk]
          _ = a ^ (k * ↑q) := by rw [← zpow_natCast (a ^ k), ← zpow_mul]
      have h2 : a ^ (k * ↑q) = a ^ (-(↑q : ℤ)) := by
        rw [zpow_eq_zpow_iff_modEq, ha_ord, Int.modEq_iff_dvd,
          show -(↑q : ℤ) - k * ↑q = -(↑q * (k + 1)) from by ring, dvd_neg,
          Nat.cast_mul, mul_comm (↑p : ℤ)]
        exact mul_dvd_mul_left ↑q hp_k1
      rw [h1, h2, zpow_neg, zpow_natCast]
    -- b commutes with d = a^p (since q | k-1)
    have hbd_comm : b * d = d * b := by
      have h1 : b * d * b⁻¹ = a ^ (k * ↑p) := by
        calc b * d * b⁻¹ = (b * a * b⁻¹) ^ (p : ℕ) := by rw [hd_def]; exact conj_pow.symm
          _ = (a ^ k) ^ (p : ℕ) := by rw [hk]
          _ = a ^ (k * ↑p) := by rw [← zpow_natCast (a ^ k), ← zpow_mul]
      have h2 : a ^ (k * ↑p) = d := by
        rw [hd_def, ← zpow_natCast, zpow_eq_zpow_iff_modEq, ha_ord,
          Int.modEq_iff_dvd, show (↑p : ℤ) - k * ↑p = -(↑p * (k - 1)) from by ring,
          dvd_neg, Nat.cast_mul]
        exact mul_dvd_mul_left ↑p hq_k1
      calc b * d = b * d * b⁻¹ * b := by group
        _ = d * b := by rw [h1, h2]
    -- c and d commute (powers of a)
    have hcd_comm : c * d = d * c := by
      rw [hc_def, hd_def]; exact (Commute.refl a).pow_pow q p
    -- Apply helper: inverted = c (order p), commuting = d (order q)
    exact nonempty_mulEquiv_prod_dihedral hq.ne_zero hp.ne_zero hqodd hpodd
      ((Nat.coprime_primes hq hp).mpr (by omega))
      c d b hc_ord hd_ord hb1 hb2 hbc_inv hbd_comm hcd_comm
      (show Nat.card G = 2 * q * p by rw [hG]; ring)
  · -- Case II: p ∣ k+1 and q ∣ k+1 → k ≡ -1 (mod pq) → dihedral
    right; left
    have hpq_k1 : (↑(p * q) : ℤ) ∣ k + 1 := by
      rw [Nat.cast_mul]
      exact IsCoprime.mul_dvd
        (by exact_mod_cast (Nat.coprime_primes hp hq).mpr (by omega)) hp_k1 hq_k1
    have hak1 : a ^ k = a⁻¹ := by
      have : a ^ (k + 1) = 1 := by
        rw [zpow_eq_one_iff_modEq, ha_ord, Int.modEq_zero_iff_dvd]; exact hpq_k1
      rw [zpow_add, zpow_one] at this; exact mul_eq_one_iff_eq_inv.mp this
    have hba_rel : b * a * b⁻¹ = a⁻¹ := by rw [← hk, hak1]
    rw [Nat.mul_assoc] at hG
    exact nonempty_mulEquiv_dihedral_odd (Nat.mul_ne_zero hp.ne_zero hq.ne_zero)
      (hpodd.mul hqodd) a b ha_ord hb1 hb2 hba_rel hG

/-! ### Exhaustiveness: `p ∣ q - 1` case (6 classes) -/

/-- The cyclic-`N` case of the order-`2pq` classification: if `G` has a normal cyclic subgroup
`N` of order `pq`, then `G` is one of the first four types (I–IV). This is exactly the
argument of `twoPQ_classification_4`, extracted so it can be reused when `p ∣ q - 1`. -/
private theorem twoPQ_classif_cyclicCase
    (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q)
    [Finite G] (hG : Nat.card G = 2 * p * q)
    (N : Subgroup G) (hNnorm : N.Normal) (hNcard : Nat.card N = p * q)
    (hcyc : IsCyclic ↥N) :
    Nonempty (G ≃* twoPQ_I p q) ∨ Nonempty (G ≃* twoPQ_II p q) ∨
    Nonempty (G ≃* twoPQ_III p q) ∨ Nonempty (G ≃* twoPQ_IV p q) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : N.Normal := hNnorm
  haveI : IsCyclic ↥N := hcyc
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  -- Step 3: get generator a of N with orderOf a = pq
  obtain ⟨a₀, ha₀⟩ := IsCyclic.exists_monoid_generator (α := ↥N)
  have ha₀_ord : orderOf a₀ = p * q :=
    (orderOf_eq_card_of_forall_mem_powers ha₀).trans hNcard
  set a := (a₀ : G) with ha_def
  have ha_ord : orderOf a = p * q := by
    change orderOf (a₀ : G) = p * q
    rw [show (a₀ : G) = N.subtype a₀ from rfl,
      orderOf_injective N.subtype N.subtype_injective, ha₀_ord]
  have ha_mem : a ∈ N := a₀.property
  -- Step 4: get involution b with orderOf b = 2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := G) 2
    ⟨p * q, by rw [hG]; ring⟩
  have hb1 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; exact absurd hb (by norm_num)
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  -- Step 5: zpowers a = N
  have hA_eq_N : zpowers a = N := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx; obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      exact N.zpow_mem ha_mem k
    · have : Nat.card ↥(zpowers a) = p * q := by rw [Nat.card_zpowers, ha_ord]
      omega
  -- Step 6: conjugation b * a * b⁻¹ = a ^ k
  have hconj_mem : b * a * b⁻¹ ∈ zpowers a := by
    rw [hA_eq_N]; exact hNnorm.conj_mem a ha_mem b
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hconj_mem
  -- Step 7: k² ≡ 1 (mod pq)
  have hbb : b * b = 1 := by rw [← pow_two]; exact hb2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hconj2 : b * (b * a * b⁻¹) * b⁻¹ = a := by
    rw [hbinv]
    calc b * (b * a * b) * b = (b * b) * a * (b * b) := by group
      _ = a := by rw [hbb, one_mul, mul_one]
  have hkk : a ^ (k * k) = a := by rw [zpow_mul, hk, conj_zpow, hk, hconj2]
  have hk1 : a ^ (k * k - 1) = 1 := by
    rw [zpow_sub, hkk, zpow_one]; exact mul_inv_cancel a
  have hpqd : (↑(p * q) : ℤ) ∣ (k - 1) * (k + 1) := by
    have h0 : (k * k - 1) ≡ 0 [ZMOD orderOf a] := zpow_eq_one_iff_modEq.mp hk1
    rw [ha_ord, Int.modEq_zero_iff_dvd] at h0
    rwa [show (k - 1) * (k + 1) = k * k - 1 by ring]
  -- Step 8: split by p and q
  have hpd : (↑p : ℤ) ∣ (k - 1) * (k + 1) :=
    dvd_trans (by exact_mod_cast dvd_mul_right p q) hpqd
  have hqd : (↑q : ℤ) ∣ (k - 1) * (k + 1) :=
    dvd_trans (by exact_mod_cast dvd_mul_left q p) hpqd
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hpd with hp_k1 | hp_k1
  <;> rcases (Nat.prime_iff_prime_int.mp hq).dvd_or_dvd hqd with hq_k1 | hq_k1
  · -- Case I: p ∣ k-1 and q ∣ k-1 → k ≡ 1 (mod pq) → abelian → cyclic
    left
    have hpq_k1 : (↑(p * q) : ℤ) ∣ k - 1 := by
      rw [Nat.cast_mul]
      exact IsCoprime.mul_dvd
        (by exact_mod_cast (Nat.coprime_primes hp hq).mpr (by omega)) hp_k1 hq_k1
    have hak1 : a ^ k = a := by
      have : a ^ (k - 1) = 1 := by
        rw [zpow_eq_one_iff_modEq, ha_ord, Int.modEq_zero_iff_dvd]; exact hpq_k1
      rw [zpow_sub, zpow_one] at this; exact mul_inv_eq_one.mp this
    have hba1 : b * a * b⁻¹ = a := by rw [← hk, hak1]
    have hcomm : Commute a b := by
      have : b * a = a * b :=
        calc b * a = b * a * b⁻¹ * b := by group
          _ = a * b := by rw [hba1]
      exact this.symm
    have hcop : (orderOf a).Coprime (orderOf b) := by
      rw [ha_ord, hb]
      exact Nat.coprime_two_right.mpr (hpodd.mul hqodd)
    haveI : IsCyclic G := by
      have hord : orderOf (a * b) = 2 * p * q := by
        rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, ha_ord, hb]; ring
      exact isCyclic_of_orderOf_eq_card (a * b) (by rw [hord, hG])
    exact cyclicRep_classification
      (Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hp.pos.ne') hq.pos.ne') hG
  · -- Case IV: p ∣ k-1 and q ∣ k+1 → ℤ/p × D_q
    right; right; right
    set c := a ^ (q : ℕ) with hc_def
    set d := a ^ (p : ℕ) with hd_def
    have hc_ord : orderOf c = p := by
      rw [hc_def, orderOf_pow' a hq.ne_zero, ha_ord,
        Nat.gcd_eq_right (dvd_mul_left q p), Nat.mul_div_cancel p hq.pos]
    have hd_ord : orderOf d = q := by
      rw [hd_def, orderOf_pow' a hp.ne_zero, ha_ord,
        Nat.gcd_eq_right (dvd_mul_right p q), Nat.mul_div_cancel_left q hp.pos]
    have hbc_comm : b * c = c * b := by
      have h1 : b * c * b⁻¹ = a ^ (k * ↑q) := by
        calc b * c * b⁻¹ = (b * a * b⁻¹) ^ (q : ℕ) := by rw [hc_def]; exact conj_pow.symm
          _ = (a ^ k) ^ (q : ℕ) := by rw [hk]
          _ = a ^ (k * ↑q) := by rw [← zpow_natCast (a ^ k), ← zpow_mul]
      have h2 : a ^ (k * ↑q) = c := by
        rw [hc_def, ← zpow_natCast, zpow_eq_zpow_iff_modEq, ha_ord,
          Int.modEq_iff_dvd, show (↑q : ℤ) - k * ↑q = -(↑q * (k - 1)) from by ring,
          dvd_neg, Nat.cast_mul, show (↑p : ℤ) * ↑q = ↑q * ↑p from mul_comm _ _]
        exact mul_dvd_mul_left ↑q hp_k1
      calc b * c = b * c * b⁻¹ * b := by group
        _ = c * b := by rw [h1, h2]
    have hbd_inv : b * d * b⁻¹ = d⁻¹ := by
      have h1 : b * d * b⁻¹ = a ^ (k * ↑p) := by
        calc b * d * b⁻¹ = (b * a * b⁻¹) ^ (p : ℕ) := by rw [hd_def]; exact conj_pow.symm
          _ = (a ^ k) ^ (p : ℕ) := by rw [hk]
          _ = a ^ (k * ↑p) := by rw [← zpow_natCast (a ^ k), ← zpow_mul]
      have h2 : a ^ (k * ↑p) = a ^ (-(↑p : ℤ)) := by
        rw [zpow_eq_zpow_iff_modEq, ha_ord, Int.modEq_iff_dvd,
          show -(↑p : ℤ) - k * ↑p = -(↑p * (k + 1)) from by ring, dvd_neg,
          Nat.cast_mul]
        exact mul_dvd_mul_left ↑p hq_k1
      rw [h1, h2, zpow_neg, zpow_natCast]
    have hdc_comm : d * c = c * d := by
      rw [hd_def, hc_def]; exact (Commute.refl a).pow_pow p q
    exact nonempty_mulEquiv_prod_dihedral hp.ne_zero hq.ne_zero hpodd hqodd
      ((Nat.coprime_primes hp hq).mpr (by omega))
      d c b hd_ord hc_ord hb1 hb2 hbd_inv hbc_comm hdc_comm
      (show Nat.card G = 2 * p * q from hG)
  · -- Case III: p ∣ k+1 and q ∣ k-1 → ℤ/q × D_p
    right; right; left
    set c := a ^ (q : ℕ) with hc_def
    set d := a ^ (p : ℕ) with hd_def
    have hc_ord : orderOf c = p := by
      rw [hc_def, orderOf_pow' a hq.ne_zero, ha_ord,
        Nat.gcd_eq_right (dvd_mul_left q p), Nat.mul_div_cancel p hq.pos]
    have hd_ord : orderOf d = q := by
      rw [hd_def, orderOf_pow' a hp.ne_zero, ha_ord,
        Nat.gcd_eq_right (dvd_mul_right p q), Nat.mul_div_cancel_left q hp.pos]
    have hbc_inv : b * c * b⁻¹ = c⁻¹ := by
      have h1 : b * c * b⁻¹ = a ^ (k * ↑q) := by
        calc b * c * b⁻¹ = (b * a * b⁻¹) ^ (q : ℕ) := by rw [hc_def]; exact conj_pow.symm
          _ = (a ^ k) ^ (q : ℕ) := by rw [hk]
          _ = a ^ (k * ↑q) := by rw [← zpow_natCast (a ^ k), ← zpow_mul]
      have h2 : a ^ (k * ↑q) = a ^ (-(↑q : ℤ)) := by
        rw [zpow_eq_zpow_iff_modEq, ha_ord, Int.modEq_iff_dvd,
          show -(↑q : ℤ) - k * ↑q = -(↑q * (k + 1)) from by ring, dvd_neg,
          Nat.cast_mul, mul_comm (↑p : ℤ)]
        exact mul_dvd_mul_left ↑q hp_k1
      rw [h1, h2, zpow_neg, zpow_natCast]
    have hbd_comm : b * d = d * b := by
      have h1 : b * d * b⁻¹ = a ^ (k * ↑p) := by
        calc b * d * b⁻¹ = (b * a * b⁻¹) ^ (p : ℕ) := by rw [hd_def]; exact conj_pow.symm
          _ = (a ^ k) ^ (p : ℕ) := by rw [hk]
          _ = a ^ (k * ↑p) := by rw [← zpow_natCast (a ^ k), ← zpow_mul]
      have h2 : a ^ (k * ↑p) = d := by
        rw [hd_def, ← zpow_natCast, zpow_eq_zpow_iff_modEq, ha_ord,
          Int.modEq_iff_dvd, show (↑p : ℤ) - k * ↑p = -(↑p * (k - 1)) from by ring,
          dvd_neg, Nat.cast_mul]
        exact mul_dvd_mul_left ↑p hq_k1
      calc b * d = b * d * b⁻¹ * b := by group
        _ = d * b := by rw [h1, h2]
    have hcd_comm : c * d = d * c := by
      rw [hc_def, hd_def]; exact (Commute.refl a).pow_pow q p
    exact nonempty_mulEquiv_prod_dihedral hq.ne_zero hp.ne_zero hqodd hpodd
      ((Nat.coprime_primes hq hp).mpr (by omega))
      c d b hc_ord hd_ord hb1 hb2 hbc_inv hbd_comm hcd_comm
      (show Nat.card G = 2 * q * p by rw [hG]; ring)
  · -- Case II: p ∣ k+1 and q ∣ k+1 → k ≡ -1 (mod pq) → dihedral
    right; left
    have hpq_k1 : (↑(p * q) : ℤ) ∣ k + 1 := by
      rw [Nat.cast_mul]
      exact IsCoprime.mul_dvd
        (by exact_mod_cast (Nat.coprime_primes hp hq).mpr (by omega)) hp_k1 hq_k1
    have hak1 : a ^ k = a⁻¹ := by
      have : a ^ (k + 1) = 1 := by
        rw [zpow_eq_one_iff_modEq, ha_ord, Int.modEq_zero_iff_dvd]; exact hpq_k1
      rw [zpow_add, zpow_one] at this; exact mul_eq_one_iff_eq_inv.mp this
    have hba_rel : b * a * b⁻¹ = a⁻¹ := by rw [← hk, hak1]
    rw [Nat.mul_assoc] at hG
    exact nonempty_mulEquiv_dihedral_odd (Nat.mul_ne_zero hp.ne_zero hq.ne_zero)
      (hpodd.mul hqodd) a b ha_ord hb1 hb2 hba_rel hG

/-- When `p ∣ q - 1`, every group of order `2pq` is isomorphic to one of the six types.
    Requires a choice of primitive `p`-th root of unity `c₀` in `(ℤ/q)ˣ` and
    a unit `d₀` of order `2p` in `(ℤ/q)ˣ`. -/
theorem twoPQ_classification_6 [NeZero p] [NeZero (2 * p)]
    (hp : p.Prime) (hq : q.Prime) (h2p : 2 < p) (hpq : p < q) (_ : p ∣ q - 1)
    (c₀ : (ZMod q)ˣ) (hc₀ : c₀ ^ p = 1) (hc₀ne : c₀ ≠ 1)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1) (hd₀ord : orderOf d₀ = 2 * p)
    [Finite G] (hG : Nat.card G = 2 * p * q) :
    Nonempty (G ≃* twoPQ_I p q) ∨ Nonempty (G ≃* twoPQ_II p q) ∨
    Nonempty (G ≃* twoPQ_III p q) ∨ Nonempty (G ≃* twoPQ_IV p q) ∨
    Nonempty (G ≃* twoPQ_V p q c₀ hc₀) ∨ Nonempty (G ≃* twoPQ_VI p q d₀ hd₀) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  -- Step 1: normal subgroup N of order pq
  obtain ⟨N, hNnorm, hNcard⟩ := twoPQ_normal_pq_subgroup p q hp hq h2p hpq hG
  haveI : N.Normal := hNnorm
  -- Step 2: N is cyclic, or non-abelian (≅ ℤ/q ⋊ ℤ/p)
  rcases classification_card_eq_prime_mul (p := q) (q := p) hq hp hpq
      (show Nat.card ↥N = q * p by rw [hNcard, mul_comm]) c₀ hc₀ hc₀ne with hcyc | hnonab
  · -- N cyclic: reduce to types I–IV
    rcases twoPQ_classif_cyclicCase p q hp hq h2p hpq hG N hNnorm hNcard hcyc with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · -- N non-abelian: types V or VI
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hncyc : ¬ IsCyclic ↥N := fun hc =>
      not_isCyclic_nonabRep hp.one_lt c₀ hc₀ hc₀ne (hnonab.some.isCyclic.mp hc)
    obtain ⟨a₁, y₁, cc, ha₁, hy₁, hccp, hcc1, hrel⟩ :=
      exists_generators_of_card_eq_prime_mul (p := q) (q := p) hq hp hpq
        (show Nat.card ↥N = q * p by rw [hNcard, mul_comm]) hncyc
    -- `zpowers a₁` is the unique Sylow-`q` of `N`, hence characteristic in `N`.
    have hqndvdp : ¬ q ∣ p := fun h => by have := Nat.le_of_dvd hp.pos h; omega
    have hfact : (Nat.card ↥N).factorization q = 1 := by
      rw [hNcard, Nat.factorization_mul hp.ne_zero hq.ne_zero, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hqndvdp, hq.factorization_self, zero_add]
    have hcard_zp : Nat.card ↥(zpowers a₁) = q ^ (Nat.card ↥N).factorization q := by
      rw [hfact, pow_one, Nat.card_zpowers, ha₁]
    let Pq : Sylow q ↥N := Sylow.ofCard (zpowers a₁) hcard_zp
    have hnq : Nat.card (Sylow q ↥N) = 1 := by
      obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥N))
      have hdvd : Nat.card (Sylow q ↥N) ∣ p * q :=
        hNcard ▸ (P0.card_dvd_index.trans (Subgroup.index_dvd_card _))
      have hndvd : ¬ q ∣ Nat.card (Sylow q ↥N) := not_dvd_card_sylow q ↥N
      have hdp : Nat.card (Sylow q ↥N) ∣ p :=
        Nat.Coprime.dvd_of_dvd_mul_right ((hq.coprime_iff_not_dvd.mpr hndvd).symm) hdvd
      rcases (Nat.dvd_prime hp).mp hdp with h | h
      · exact h
      · exfalso
        have hmod := card_sylow_modEq_one q ↥N
        rw [h] at hmod
        have hd : q ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
        have := Nat.le_of_dvd (by omega) hd
        omega
    haveI : Subsingleton (Sylow q ↥N) := (Nat.card_eq_one_iff_unique.mp hnq).1
    haveI hzp_char : (zpowers a₁).Characteristic :=
      Sylow.characteristic_of_normal Pq (Sylow.normal_of_subsingleton Pq)
    set a : G := (a₁ : G) with ha_def
    have ha_ord : orderOf a = q := by
      rw [ha_def, show (a₁ : G) = N.subtype a₁ from rfl,
        orderOf_injective N.subtype N.subtype_injective, ha₁]
    have hQ_normal : (zpowers a).Normal := by
      have heq : zpowers a = (zpowers a₁).map N.subtype := by
        rw [ha_def, show (a₁ : G) = N.subtype a₁ from rfl, MonoidHom.map_zpowers]
      rw [heq]; infer_instance
    -- the involution `b`
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 ⟨p * q, by rw [hG]; ring⟩
    have hb1 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; exact absurd hb (by norm_num)
    have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
    have hbb : b * b = 1 := by rw [← pow_two]; exact hb2
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
    -- conjugation `b * a * b⁻¹ = a ^ k`, with `k² ≡ 1 (mod q)`
    have hconj_mem : b * a * b⁻¹ ∈ zpowers a := hQ_normal.conj_mem a (mem_zpowers a) b
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hconj_mem
    have hconj2 : b * (b * a * b⁻¹) * b⁻¹ = a := by
      rw [hbinv]
      calc b * (b * a * b) * b = (b * b) * a * (b * b) := by group
        _ = a := by rw [hbb, one_mul, mul_one]
    have hkk : a ^ (k * k) = a := by rw [zpow_mul, hk, conj_zpow, hk, hconj2]
    have hk1 : a ^ (k * k - 1) = 1 := by
      rw [zpow_sub, hkk, zpow_one]; exact mul_inv_cancel a
    have hqd : (↑q : ℤ) ∣ (k - 1) * (k + 1) := by
      have h0 : (k * k - 1) ≡ 0 [ZMOD orderOf a] := zpow_eq_one_iff_modEq.mp hk1
      rw [ha_ord, Int.modEq_zero_iff_dvd] at h0
      rwa [show (k - 1) * (k + 1) = k * k - 1 by ring]
    -- lift the order-`p` generator and its conjugation relation
    set y : G := (y₁ : G) with hy_def
    have hy_ord : orderOf y = p := by
      rw [hy_def, show (y₁ : G) = N.subtype y₁ from rfl,
        orderOf_injective N.subtype N.subtype_injective, hy₁]
    have hyrel : y * a * y⁻¹ = a ^ (cc : ZMod q).val := by
      have hh := congrArg (N.subtype) hrel
      simpa [hy_def, ha_def, map_mul, map_inv, map_pow] using hh
    rcases (Nat.prime_iff_prime_int.mp hq).dvd_or_dvd hqd with hk_neg | hk_pos
    · -- `q ∣ k - 1`: `b` centralizes `a`  → type V
      haveI : Fact q.Prime := ⟨hq⟩
      have hba1 : b * a * b⁻¹ = a := by
        have hak : a ^ k = a := by
          have hh : a ^ (k - 1) = 1 := by
            rw [zpow_eq_one_iff_modEq, ha_ord, Int.modEq_zero_iff_dvd]; exact hk_neg
          rw [zpow_sub, zpow_one] at hh; exact mul_inv_eq_one.mp hh
        rw [← hk, hak]
      have hab_comm : Commute a b := by
        have hh : b * a = a * b := by
          calc b * a = b * a * b⁻¹ * b := by group
            _ = a * b := by rw [hba1]
        exact hh.symm
      -- the centralizer of `a₁` in `N` is `⟨a₁⟩`
      have cent_aN : ∀ w₀ : ↥N, Commute w₀ a₁ → w₀ ∈ zpowers a₁ := by
        intro w₀ hcw
        by_cases hpdvd : p ∣ orderOf w₀
        · exfalso
          obtain ⟨j, hj⟩ := hpdvd
          have hord_pos : 0 < orderOf w₀ := orderOf_pos w₀
          have hjne : j ≠ 0 := by rintro rfl; simp [hj] at hord_pos
          have hn'_ord : orderOf (w₀ ^ j) = p := by
            rw [orderOf_pow' w₀ hjne, hj, Nat.gcd_eq_right (dvd_mul_left j p),
              Nat.mul_div_cancel p (Nat.pos_of_ne_zero hjne)]
          have hcomm_an : Commute a₁ (w₀ ^ j) := (hcw.symm).pow_right j
          have hcop : Nat.Coprime (orderOf a₁) (orderOf (w₀ ^ j)) := by
            rw [ha₁, hn'_ord]; exact (Nat.coprime_primes hq hp).mpr (by omega)
          have hord_mul : orderOf (a₁ * w₀ ^ j) = p * q := by
            rw [hcomm_an.orderOf_mul_eq_mul_orderOf_of_coprime hcop, ha₁, hn'_ord]; ring
          haveI : IsCyclic ↥N :=
            isCyclic_of_orderOf_eq_card (a₁ * w₀ ^ j) (by rw [hord_mul, hNcard])
          exact hncyc inferInstance
        · have hdvd : orderOf w₀ ∣ p * q := by
            rw [← hNcard]; exact orderOf_dvd_natCard _
          have hdq : orderOf w₀ ∣ q :=
            ((hp.coprime_iff_not_dvd.mpr hpdvd).symm).dvd_of_dvd_mul_left hdvd
          rcases (Nat.dvd_prime hq).mp hdq with h1 | h1
          · rw [orderOf_eq_one_iff] at h1; rw [h1]; exact one_mem _
          · have hpg : IsPGroup q ↥(zpowers w₀) :=
              IsPGroup.of_card (by rw [Nat.card_zpowers, h1]; exact (pow_one q).symm)
            obtain ⟨Q', hQ'⟩ := hpg.exists_le_sylow
            rw [Subsingleton.elim Q' Pq] at hQ'
            exact hQ' (mem_zpowers w₀)
      -- `b` commutes with `y`, hence is central
      have haN : a ∈ N := by rw [ha_def]; exact SetLike.coe_mem a₁
      have hyN : y ∈ N := by rw [hy_def]; exact SetLike.coe_mem y₁
      have hbab : b⁻¹ * a * b = a := by
        rw [hbinv]; have h := hba1; rwa [hbinv] at h
      have hyb_comm : b * y = y * b := by
        set z := b * y * b⁻¹ with hz_def
        have hzN : z ∈ N := hNnorm.conj_mem y hyN b
        have hzconj : z * a * z⁻¹ = a ^ (cc : ZMod q).val := by
          rw [hz_def]
          calc b * y * b⁻¹ * a * (b * y * b⁻¹)⁻¹
              = b * (y * (b⁻¹ * a * b) * y⁻¹) * b⁻¹ := by group
            _ = b * (y * a * y⁻¹) * b⁻¹ := by rw [hbab]
            _ = b * a ^ (cc : ZMod q).val * b⁻¹ := by rw [hyrel]
            _ = a ^ (cc : ZMod q).val := by rw [← conj_pow, hba1]
        have hcomm_yz : Commute (y⁻¹ * z) a := by
          change (y⁻¹ * z) * a = a * (y⁻¹ * z)
          have h1 : (y⁻¹ * z) * a * (y⁻¹ * z)⁻¹ = a := by
            have hrw : (y⁻¹ * z) * a * (y⁻¹ * z)⁻¹ = y⁻¹ * (z * a * z⁻¹) * y := by group
            rw [hrw, hzconj]
            calc y⁻¹ * a ^ (cc : ZMod q).val * y = y⁻¹ * (y * a * y⁻¹) * y := by rw [hyrel]
              _ = a := by group
          calc (y⁻¹ * z) * a
              = (y⁻¹ * z) * a * (y⁻¹ * z)⁻¹ * (y⁻¹ * z) := by group
            _ = a * (y⁻¹ * z) := by rw [h1]
        have hmemyz : y⁻¹ * z ∈ N := N.mul_mem (N.inv_mem hyN) hzN
        set w₀ : ↥N := ⟨y⁻¹ * z, hmemyz⟩ with hw₀_def
        have hcw₀ : Commute w₀ a₁ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          exact hcomm_yz
        obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (cent_aN w₀ hcw₀)
        have hzeq : z = y * a ^ m := by
          have hsub : a ^ m = y⁻¹ * z := by
            have hc := congrArg (N.subtype) hm
            simpa [map_zpow, hw₀_def] using hc
          rw [hsub, ← mul_assoc, mul_inv_cancel, one_mul]
        have hba_m : b * a ^ m * b⁻¹ = a ^ m := by rw [← conj_zpow, hba1]
        have hbzb : b * z * b⁻¹ = y := by
          rw [hz_def, hbinv]
          calc b * (b * y * b) * b = (b * b) * y * (b * b) := by group
            _ = y := by rw [hbb, one_mul, mul_one]
        have hbzb2 : b * z * b⁻¹ = y * a ^ (2 * m) := by
          rw [hzeq]
          calc b * (y * a ^ m) * b⁻¹ = (b * y * b⁻¹) * (b * a ^ m * b⁻¹) := by group
            _ = z * a ^ m := by rw [← hz_def, hba_m]
            _ = (y * a ^ m) * a ^ m := by rw [hzeq]
            _ = y * a ^ (2 * m) := by rw [mul_assoc, ← zpow_add, two_mul]
        have ha2m : a ^ (2 * m) = 1 := by
          have heqy : y * a ^ (2 * m) = y * 1 := by rw [mul_one, ← hbzb2, hbzb]
          exact mul_left_cancel heqy
        have hqdvd : (↑q : ℤ) ∣ m := by
          have h2m : (↑q : ℤ) ∣ 2 * m := by
            have hh := zpow_eq_one_iff_modEq.mp ha2m
            rwa [ha_ord, Int.modEq_zero_iff_dvd] at hh
          rcases (Nat.prime_iff_prime_int.mp hq).dvd_or_dvd h2m with h | h
          · exfalso
            have h2 : (q : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h
            have : q ≤ 2 := by exact_mod_cast h2
            omega
          · exact h
        have ham1 : a ^ m = 1 := by
          rw [zpow_eq_one_iff_modEq, ha_ord, Int.modEq_zero_iff_dvd]; exact hqdvd
        have hzy : b * y * b⁻¹ = y := by rw [← hz_def, hzeq, ham1, mul_one]
        exact mul_inv_eq_iff_eq_mul.mp hzy
      -- `b` commutes with all of `N`
      haveI : Fintype ↥N := Fintype.ofFinite ↥N
      have ha_in : a ∈ Subgroup.closure ({a, y} : Set G) := Subgroup.subset_closure (by simp)
      have hy_in : y ∈ Subgroup.closure ({a, y} : Set G) := Subgroup.subset_closure (by simp)
      have hle : Subgroup.closure ({a, y} : Set G) ≤ N := by
        rw [Subgroup.closure_le]; intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact haN
        · exact hyN
      have hpq_dvd : p * q ∣ Nat.card ↥(Subgroup.closure ({a, y} : Set G)) :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp hq).mpr (by omega))
          (by rw [← hy_ord]; exact Subgroup.orderOf_dvd_natCard _ hy_in)
          (by rw [← ha_ord]; exact Subgroup.orderOf_dvd_natCard _ ha_in)
      have hgen : Subgroup.closure ({a, y} : Set G) = N :=
        Subgroup.eq_of_le_of_card_ge hle
          (le_trans (le_of_eq hNcard) (Nat.le_of_dvd Nat.card_pos hpq_dvd))
      have hbcent : ∀ n : G, n ∈ N → Commute b n := by
        intro n hn
        rw [← hgen] at hn
        induction hn using Subgroup.closure_induction with
        | mem x hx =>
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with rfl | rfl
            · exact hab_comm.symm
            · exact hyb_comm
        | one => exact Commute.one_right b
        | mul x z _ _ hx hz => exact hx.mul_right hz
        | inv x _ hx => exact hx.inv_right
      have hbnotN : b ∉ N := by
        intro hbN
        have h2 : (2 : ℕ) ∣ Nat.card ↥N := by rw [← hb]; exact Subgroup.orderOf_dvd_natCard N hbN
        rw [hNcard] at h2
        have hodd : Odd (p * q) :=
          (hp.odd_of_ne_two (by omega)).mul (hq.odd_of_ne_two (by omega))
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
      -- the product isomorphism `G ≃* ↥N × ℤ/2`
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hb_add : ∀ i j : ZMod 2, b ^ (i + j).val = b ^ i.val * b ^ j.val := by
        intro i j; rw [← pow_add]; apply pow_eq_pow_iff_modEq.mpr
        rw [hb, ZMod.val_add]; exact Nat.mod_modEq _ _
      let Φ : ↥N × Multiplicative (ZMod 2) → G := fun z =>
        (z.1 : G) * b ^ (Multiplicative.toAdd z.2).val
      have hΦmul : ∀ z w, Φ (z * w) = Φ z * Φ w := by
        rintro ⟨n₁, ε₁⟩ ⟨n₂, ε₂⟩
        change (↑(n₁ * n₂) : G) * b ^ (Multiplicative.toAdd (ε₁ * ε₂)).val
            = ((↑n₁ : G) * b ^ (Multiplicative.toAdd ε₁).val)
              * ((↑n₂ : G) * b ^ (Multiplicative.toAdd ε₂).val)
        rw [Subgroup.coe_mul,
          show Multiplicative.toAdd (ε₁ * ε₂)
              = Multiplicative.toAdd ε₁ + Multiplicative.toAdd ε₂ from rfl, hb_add]
        have hBP := ((hbcent n₂ (SetLike.coe_mem n₂)).pow_left
          (Multiplicative.toAdd ε₁).val).symm.eq
        rw [mul_assoc (↑n₁ : G) (↑n₂ : G) (b ^ (Multiplicative.toAdd ε₁).val
              * b ^ (Multiplicative.toAdd ε₂).val),
          ← mul_assoc (↑n₂ : G) (b ^ (Multiplicative.toAdd ε₁).val)
              (b ^ (Multiplicative.toAdd ε₂).val),
          hBP,
          mul_assoc (b ^ (Multiplicative.toAdd ε₁).val) (↑n₂ : G)
              (b ^ (Multiplicative.toAdd ε₂).val),
          ← mul_assoc (↑n₁ : G) (b ^ (Multiplicative.toAdd ε₁).val)
              ((↑n₂ : G) * b ^ (Multiplicative.toAdd ε₂).val)]
      let f : ↥N × Multiplicative (ZMod 2) →* G := MonoidHom.mk' Φ hΦmul
      have hinj : Function.Injective f := by
        rw [injective_iff_map_eq_one]
        rintro ⟨n, ε⟩ hx
        have hx' : (↑n : G) * b ^ (Multiplicative.toAdd ε).val = 1 := hx
        have hvlt : (Multiplicative.toAdd ε).val < 2 := ZMod.val_lt _
        rcases (by omega : (Multiplicative.toAdd ε).val = 0 ∨
            (Multiplicative.toAdd ε).val = 1) with h | h
        · rw [h, pow_zero, mul_one] at hx'
          have hn1 : n = 1 := by apply Subtype.ext; rw [Subgroup.coe_one]; exact hx'
          have hε1 : ε = 1 := by
            have hz : Multiplicative.toAdd ε = 0 := (ZMod.val_eq_zero _).mp h
            rw [← ofAdd_toAdd ε, hz, ofAdd_zero]
          rw [hn1, hε1]; rfl
        · exfalso
          rw [h, pow_one] at hx'
          have hbe : b = (↑n : G)⁻¹ := eq_inv_of_mul_eq_one_right hx'
          exact hbnotN (by rw [hbe]; exact N.inv_mem (SetLike.coe_mem n))
      have hcard_eq : Fintype.card (↥N × Multiplicative (ZMod 2)) = Fintype.card G := by
        rw [Fintype.card_prod]
        have h1 : Fintype.card ↥N = p * q := by rw [← Nat.card_eq_fintype_card, hNcard]
        have h2 : Fintype.card (Multiplicative (ZMod 2)) = 2 :=
          (Fintype.card_congr Multiplicative.toAdd).trans (ZMod.card 2)
        rw [h1, h2, ← Nat.card_eq_fintype_card, hG]; ring
      have hbij : Function.Bijective f :=
        (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard_eq⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨((MulEquiv.ofBijective f hbij).symm).trans
          (hnonab.some.prodCongr (MulEquiv.refl (Multiplicative (ZMod 2))))⟩))))
    · -- `q ∣ k + 1`: `b` inverts `a` → type VI
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Fact (1 < q) := ⟨hq.one_lt⟩
      have hba : b * a * b⁻¹ = a⁻¹ := by
        have hak : a ^ k = a⁻¹ := by
          have hh : a ^ (k + 1) = 1 := by
            rw [zpow_eq_one_iff_modEq, ha_ord, Int.modEq_zero_iff_dvd]; exact hk_pos
          rw [zpow_add, zpow_one] at hh; exact mul_eq_one_iff_eq_inv.mp hh
        rw [← hk, hak]
      -- the unit `u = -cc` has order `2p`
      have hcc_ord : orderOf cc = p := orderOf_eq_prime hccp hcc1
      have hneg1_val_ne : (-1 : ZMod q) ≠ 1 :=
        Ring.neg_one_ne_one_of_char_ne_two (by rw [ZMod.ringChar_zmod_n]; omega)
      have hneg1_ne : (-1 : (ZMod q)ˣ) ≠ 1 := fun h =>
        hneg1_val_ne (by have := congrArg Units.val h; simpa using this)
      have hneg1_ord : orderOf (-1 : (ZMod q)ˣ) = 2 := orderOf_eq_prime (by simp) hneg1_ne
      set u : (ZMod q)ˣ := -cc with hu_def
      have hu_ord : orderOf u = 2 * p := by
        have : orderOf ((-1 : (ZMod q)ˣ) * cc) = orderOf (-1 : (ZMod q)ˣ) * orderOf cc :=
          (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime (by
            rw [hneg1_ord, hcc_ord]
            exact Nat.coprime_two_left.mpr (hp.odd_of_ne_two (by omega)))
        rw [hu_def, show (-cc : (ZMod q)ˣ) = (-1) * cc from (neg_one_mul cc).symm, this,
          hneg1_ord, hcc_ord]
      -- conjugation by `w = y * b`
      set w : G := y * b with hw_def
      have hwconj_raw : w * a * w⁻¹ = (a ^ (cc : ZMod q).val)⁻¹ := by
        rw [hw_def, mul_inv_rev, hbinv]
        calc y * b * a * (b * y⁻¹) = y * (b * a * b⁻¹) * y⁻¹ := by rw [hbinv]; group
          _ = y * a⁻¹ * y⁻¹ := by rw [hba]
          _ = (y * a * y⁻¹)⁻¹ := by group
          _ = (a ^ (cc : ZMod q).val)⁻¹ := by rw [hyrel]
      have hcast_u : ((u : ZMod q).val : ZMod q) = (u : ZMod q) := ZMod.natCast_rightInverse _
      have hcast_cc : ((cc : ZMod q).val : ZMod q) = (cc : ZMod q) := ZMod.natCast_rightInverse _
      have hu_val : a ^ ((u : ZMod q)).val = (a ^ (cc : ZMod q).val)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_add, ← orderOf_dvd_iff_pow_eq_one, ha_ord,
          ← CharP.cast_eq_zero_iff (ZMod q) q ((u : ZMod q).val + (cc : ZMod q).val),
          Nat.cast_add, hcast_u, hcast_cc, hu_def, Units.val_neg]
        ring
      have hwconj : w * a * w⁻¹ = a ^ (u : ZMod q).val := by rw [hwconj_raw, hu_val]
      -- iterate conjugation
      have conj_iter : ∀ (g : G) (v : (ZMod q)ˣ), g * a * g⁻¹ = a ^ (v : ZMod q).val →
          ∀ n : ℕ, g ^ n * a * (g ^ n)⁻¹ = a ^ ((v ^ n : (ZMod q)ˣ) : ZMod q).val := by
        intro g v hgv n
        induction n with
        | zero => simp [ZMod.val_one]
        | succ m ih =>
          have hsplit : g ^ (m + 1) * a * (g ^ (m + 1))⁻¹
              = g * (g ^ m * a * (g ^ m)⁻¹) * g⁻¹ := by rw [pow_succ, mul_inv_rev]; group
          rw [hsplit, ih, ← conj_pow, hgv, ← pow_mul]
          apply pow_eq_pow_iff_modEq.mpr
          rw [ha_ord, show (((v ^ (m + 1) : (ZMod q)ˣ) : ZMod q)).val
                = ((v : ZMod q).val * (((v ^ m : (ZMod q)ˣ) : ZMod q)).val) % q from by
              rw [pow_succ', Units.val_mul, ZMod.val_mul]]
          exact (Nat.mod_modEq _ _).symm
      have conj_order : ∀ (g : G) (v : (ZMod q)ˣ), g * a * g⁻¹ = a ^ (v : ZMod q).val →
          v ^ orderOf g = 1 := by
        intro g v hgv
        have h1 := conj_iter g v hgv (orderOf g)
        rw [pow_orderOf_eq_one g] at h1
        simp only [one_mul, inv_one, mul_one] at h1
        have hmod : ((v ^ orderOf g : (ZMod q)ˣ) : ZMod q).val ≡ 1 [MOD q] := by
          have h2 : a ^ 1 = a ^ ((v ^ orderOf g : (ZMod q)ˣ) : ZMod q).val := by
            rw [pow_one]; exact h1
          have h3 := (pow_eq_pow_iff_modEq.mp h2).symm
          rwa [ha_ord] at h3
        have hval1 : ((v ^ orderOf g : (ZMod q)ˣ) : ZMod q).val = 1 := by
          have hlt := ZMod.val_lt ((v ^ orderOf g : (ZMod q)ˣ) : ZMod q)
          unfold Nat.ModEq at hmod
          rw [Nat.mod_eq_of_lt hq.one_lt, Nat.mod_eq_of_lt hlt] at hmod
          exact hmod
        have hcast : ((v ^ orderOf g : (ZMod q)ˣ) : ZMod q) = 1 := by
          conv_lhs => rw [← ZMod.natCast_rightInverse ((v ^ orderOf g : (ZMod q)ˣ) : ZMod q)]
          rw [hval1, Nat.cast_one]
        exact Units.val_eq_one.mp hcast
      -- relabel `d₀ = u ^ j₀`
      have hcoprime : Nat.Coprime q (2 * p) :=
        Nat.Coprime.mul_right (Nat.coprime_two_right.mpr (hq.odd_of_ne_two (by omega)))
          ((Nat.coprime_primes hq hp).mpr (by omega))
      have hcardG : Nat.card G = q * (2 * p) := by rw [hG]; ring
      have hd₀ne : d₀ ≠ 1 := by
        intro h; rw [h, orderOf_one] at hd₀ord; have := NeZero.ne (2 * p); omega
      obtain ⟨j₀, hj₀⟩ := (mem_powers_iff_mem_zpowers (y := d₀)).mpr
        (unit_mem_zpowers_of_pow_eq (p := q) (q := 2 * p) hq (by positivity) u d₀ hu_ord hd₀)
      simp only at hj₀
      have hj₀ne : j₀ ≠ 0 := by intro h; rw [h, pow_zero] at hj₀; exact hd₀ne hj₀.symm
      set w' : G := w ^ j₀ with hw'_def
      have hw'conj : w' * a * w'⁻¹ = a ^ (d₀ : ZMod q).val := by
        rw [hw'_def, conj_iter w u hwconj j₀, hj₀]
      have hw'ord : orderOf w' = 2 * p := by
        have h2p_dvd : 2 * p ∣ orderOf w' := by
          have hpow := conj_order w' d₀ hw'conj
          rw [← hd₀ord]; exact orderOf_dvd_of_pow_eq_one hpow
        have hdvd : orderOf w' ∣ 2 * p * q := by
          rw [← hG, Nat.card_eq_fintype_card]; exact orderOf_dvd_card
        have hne : orderOf w' ≠ 2 * p * q := by
          intro h
          haveI : IsCyclic G := isCyclic_of_orderOf_eq_card w' (by rw [h, hG])
          exact hncyc inferInstance
        obtain ⟨t, ht⟩ := h2p_dvd
        rw [ht] at hdvd hne ⊢
        have htq : t ∣ q :=
          (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 * p)).mp hdvd
        rcases (Nat.dvd_prime hq).mp htq with h | h
        · rw [h, mul_one]
        · exact absurd (by rw [h]) hne
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (nonempty_mulEquiv_nonabRep (p := q) (q := 2 * p) a w' ha_ord hw'ord d₀ hd₀
          hw'conj hcoprime hcardG)))))


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

/-- **II ≇ VI**: both have trivial center, so we distinguish them by a different
invariant: `D_{pq}` has an element of order `pq` (the rotation `r 1`), but in the
faithful semidirect product `ℤ/q ⋊ ℤ/2p` every element is conjugate either into the
cyclic factor `ℤ/q` (order dividing `q`) or into the complement `ℤ/2p` (order dividing
`2p`), so no element has order `pq`. -/
theorem twoPQ_II_not_VI [NeZero (2 * p)]
    (hp : p.Prime) (hq : q.Prime)
    (h2p : 2 < p) (hpq : p < q)
    (d₀ : (ZMod q)ˣ) (hd₀ : d₀ ^ (2 * p) = 1) (hd₀ord : orderOf d₀ = 2 * p) :
    ¬ Nonempty (twoPQ_II p q ≃* twoPQ_VI p q d₀ hd₀) := by
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hHcard : Fintype.card (Multiplicative (ZMod (2 * p))) = 2 * p :=
    (Fintype.card_congr Multiplicative.toAdd).trans (ZMod.card (2 * p))
  -- Type VI has no element of order `p * q`.
  have no_order_pq : ∀ g : twoPQ_VI p q d₀ hd₀, orderOf g ≠ p * q := by
    intro g hord
    by_cases hgr : g.right = 1
    · -- `g` lies in the `ℤ/q` factor, so its order divides `q`.
      have hg_inl : g = SemidirectProduct.inl g.left := by
        apply SemidirectProduct.ext
        · rw [SemidirectProduct.left_inl]
        · rw [SemidirectProduct.right_inl]; exact hgr
      have hdvd : orderOf g ∣ q := by
        rw [hg_inl, orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective]
        have hNcard : Fintype.card (Multiplicative (ZMod q)) = q :=
          (Fintype.card_congr Multiplicative.toAdd).trans (ZMod.card q)
        have hdc := orderOf_dvd_card (x := g.left)
        rw [hNcard] at hdc
        exact hdc
      rw [hord] at hdvd
      have hpdvd : p ∣ q := dvd_trans (dvd_mul_right p q) hdvd
      have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpdvd
      omega
    · -- `g.right ≠ 1`: `g` is conjugate to `inr g.right`, so its order divides `2 * p`.
      set h := g.right with hh_def
      set v := g.left with hv_def
      set j := Multiplicative.toAdd h with hj_def
      have hj_ne : j ≠ 0 := by
        intro hj
        apply hgr
        rw [← ofAdd_toAdd h, ← hj_def, hj, ofAdd_zero]
      have hd0_ne : d₀ ^ j.val ≠ 1 := by
        intro hpow
        have hdvd : orderOf d₀ ∣ j.val := orderOf_dvd_of_pow_eq_one hpow
        rw [hd₀ord] at hdvd
        have hlt : j.val < 2 * p := ZMod.val_lt j
        have hne0 : j.val ≠ 0 := by rw [Ne, ZMod.val_eq_zero]; exact hj_ne
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne0) hdvd
        omega
      set ζ : ZMod q := ((d₀ ^ j.val : (ZMod q)ˣ) : ZMod q) with hζ_def
      have hζ_ne : ζ ≠ 1 := by
        rw [hζ_def]; intro hz; exact hd0_ne (Units.val_eq_one.mp hz)
      set U : ZMod q := (ζ - 1)⁻¹ * Multiplicative.toAdd v with hU_def
      set u₀ : Multiplicative (ZMod q) := Multiplicative.ofAdd U with hu_def
      have hAdd : U + Multiplicative.toAdd v = ζ * U := by
        have hsub : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ_ne
        rw [hU_def]; field_simp; ring
      have e1 : u₀ * v = Multiplicative.ofAdd (U + Multiplicative.toAdd v) := by
        rw [hu_def, ofAdd_add, ofAdd_toAdd]
      have e2 : (actionHom d₀ hd₀ h) u₀ = Multiplicative.ofAdd (ζ * U) := by
        rw [hu_def, show h = Multiplicative.ofAdd j from (ofAdd_toAdd h).symm, actionHom_apply,
          ← hζ_def]
      have key_eq : u₀ * v = (actionHom d₀ hd₀ h) u₀ := by
        rw [e1, e2]; exact congrArg Multiplicative.ofAdd hAdd
      have hconj : SemidirectProduct.inl u₀ * g * (SemidirectProduct.inl u₀)⁻¹
          = SemidirectProduct.inr h := by
        apply SemidirectProduct.ext
        · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
            SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
            SemidirectProduct.left_inr, map_one, MulAut.one_apply, inv_one, one_mul]
          rw [map_inv, ← key_eq, mul_inv_cancel]
        · simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right, hh_def]
      have hh2p : h ^ (2 * p) = 1 := by
        have hpc : h ^ Fintype.card (Multiplicative (ZMod (2 * p))) = 1 := pow_card_eq_one
        rwa [hHcard] at hpc
      have hg2p : g ^ (2 * p) = 1 := by
        have key : SemidirectProduct.inl u₀ * g ^ (2 * p) * (SemidirectProduct.inl u₀)⁻¹ = 1 := by
          rw [← conj_pow, hconj, ← map_pow, hh2p, map_one]
        calc g ^ (2 * p)
            = (SemidirectProduct.inl u₀)⁻¹
                * (SemidirectProduct.inl u₀ * g ^ (2 * p) * (SemidirectProduct.inl u₀)⁻¹)
                * SemidirectProduct.inl u₀ := by group
          _ = (SemidirectProduct.inl u₀)⁻¹ * 1 * SemidirectProduct.inl u₀ := by rw [key]
          _ = 1 := by group
      have hco : orderOf g ∣ 2 * p := orderOf_dvd_of_pow_eq_one hg2p
      have hpq_dvd : p * q ∣ 2 * p := by rw [← hord]; exact hco
      have hqdvd : q ∣ 2 * p := dvd_trans (dvd_mul_left q p) hpq_dvd
      rcases hq.dvd_mul.mp hqdvd with h2 | hp2
      · have := Nat.le_of_dvd (by norm_num) h2; omega
      · have := Nat.le_of_dvd hp.pos hp2; omega
  rintro ⟨e⟩
  exact no_order_pq (e (DihedralGroup.r 1)) (by
    rw [MulEquiv.orderOf_eq]; exact DihedralGroup.orderOf_r_one)


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
           exact absurd hiso (twoPQ_II_not_VI p q hp hq h2p hpq d₀ hd₀ hd₀ord))
        | (dsimp [rep6] at hiso;
           exact absurd (hiso.map MulEquiv.symm)
             (twoPQ_II_not_VI p q hp hq h2p hpq d₀ hd₀ hd₀ord))

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



end Smallgroups.UsefulTheorems
