/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic.NormNum.Prime

/-!
# Groups of order 60: Sylow-5 counting and simplicity

`60 = 2² · 3 · 5`.  This file proves the first steps of the classification of
groups of order `60`:

* `card_sylow_5_of_card_60`: a group of order `60` has `1` or `6` Sylow
  `5`-subgroups;
* `isSimpleGroup_of_card_60_of_card_sylow_5_eq_six`: if it has `6` Sylow
  `5`-subgroups, then it is simple.

The simplicity proof follows the classical argument, with all element-counting
steps replaced by Burnside's normal `p`-complement theorem
(`MonoidHom.ker_transferSylow_isComplement'`):

* a normal subgroup `N` with `5 ∣ |N|` contains **every** Sylow `5`-subgroup
  (they are all conjugate and `N` is normal), so `Sylow 5 N` has at least `6`
  elements, forcing `|N| ∈ {30, 60}`;
* a group of order `30` has a normal subgroup of order `5`: if `n₅ = 6` the
  Sylow `5`-subgroup is self-normalizing, so Burnside gives a normal
  complement of order `6`, whose unique Sylow `3`-subgroup is characteristic;
  passing to the order-`10` quotient and pulling back yields a normal subgroup
  of order `15`, whose unique Sylow `5`-subgroup is characteristic, hence
  normal in the whole group;
* normal subgroups of order `2`, `3`, `4` are excluded by pulling back a
  normal order-`5` subgroup of the quotient (of order `30`, `20` or `15`),
  producing a normal subgroup of order `10`, `15` or `20` — contradicting the
  first bullet;
* normal subgroups of order `6` and `12` contain a characteristic subgroup of
  order `3` or `4` (for order `12` with four Sylow `3`-subgroups this is again
  Burnside), reducing to the previous case.
-/

namespace Smallgroups.UsefulTheorems

open Subgroup Pointwise

variable {G : Type*} [Group G]

/-! ### Generic Sylow-counting helpers -/

section SylowCount

variable {H : Type*} [Group H] [Finite H]

/-- If `|H| = k * p` with `p` prime, the number of Sylow `p`-subgroups
divides `k`. -/
private lemma card_sylow_dvd_of_card_eq_mul {p k : ℕ} [hp : Fact p.Prime]
    (hH : Nat.card H = k * p) :
    Nat.card (Sylow p H) ∣ k := by
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow p H))
  have hndvd : ¬ p ∣ Nat.card (Sylow p H) := not_dvd_card_sylow p H
  have hdvd : Nat.card (Sylow p H) ∣ k * p := by
    rw [← hH]
    exact P0.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have hcop : Nat.Coprime (Nat.card (Sylow p H)) p :=
    (hp.out.coprime_iff_not_dvd.mpr hndvd).symm
  exact hcop.dvd_of_dvd_mul_right hdvd

/-- The `p`-factorization of `k * p` is `1` when `p ∤ k`. -/
private lemma factorization_mul_self {p k : ℕ} (hp : p.Prime) (hpk : ¬ p ∣ k) :
    (k * p).factorization p = 1 := by
  have hk0 : k ≠ 0 := fun h => hpk (h ▸ dvd_zero p)
  rw [Nat.factorization_mul hk0 hp.ne_zero, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpk, hp.factorization_self, zero_add]

/-- If `|H| = k * p` with `p ∤ k`, every Sylow `p`-subgroup has order `p`. -/
private lemma card_sylow_subgroup_eq_prime {p k : ℕ} [hp : Fact p.Prime]
    (hH : Nat.card H = k * p) (hpk : ¬ p ∣ k) (P : Sylow p H) :
    Nat.card (P : Subgroup H) = p := by
  rw [Sylow.card_eq_multiplicity, hH, factorization_mul_self hp.out hpk, pow_one]

/-- A unique Sylow `p`-subgroup (of order `p`) is a characteristic subgroup. -/
private lemma exists_char_of_card_sylow_eq_one {p k : ℕ} [hp : Fact p.Prime]
    (hH : Nat.card H = k * p) (hpk : ¬ p ∣ k)
    (h1 : Nat.card (Sylow p H) = 1) :
    ∃ R : Subgroup H, R.Characteristic ∧ Nat.card R = p := by
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p H))
  haveI : Subsingleton (Sylow p H) := (Nat.card_eq_one_iff_unique.mp h1).1
  have hnorm : (P : Subgroup H).Normal := Sylow.normal_of_subsingleton P
  have hchar : (P : Subgroup H).Characteristic := Sylow.characteristic_of_normal P hnorm
  exact ⟨P, hchar, card_sylow_subgroup_eq_prime hH hpk P⟩

/-- **Burnside's normal complement** for a self-normalizing Sylow subgroup of
prime order: if `|H| = k * p` with `p ∤ k` and `H` has exactly `k` Sylow
`p`-subgroups (the maximum possible number), then `H` has a normal subgroup of
order `k`. -/
private lemma exists_normal_complement_of_card_sylow_eq {p k : ℕ} [hp : Fact p.Prime]
    (hH : Nat.card H = k * p) (hpk : ¬ p ∣ k)
    (hnp : Nat.card (Sylow p H) = k) :
    ∃ K : Subgroup H, K.Normal ∧ Nat.card K = k := by
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p H))
  have hPcard : Nat.card (P : Subgroup H) = p := card_sylow_subgroup_eq_prime hH hpk P
  have hk0 : k ≠ 0 := fun h => hpk (h ▸ dvd_zero p)
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  -- the normalizer of `P` is `P` itself
  have hidx : (Subgroup.normalizer (P : Set H)).index = k := by
    rw [← Sylow.card_eq_index_normalizer]; exact hnp
  have hncard : Nat.card (Subgroup.normalizer (P : Set H)) = p := by
    have hmi := Subgroup.card_mul_index (Subgroup.normalizer (P : Set H))
    rw [hidx, hH] at hmi
    have h2 : Nat.card (Subgroup.normalizer (P : Set H)) * k = p * k := by
      rw [hmi]; ring
    exact Nat.eq_of_mul_eq_mul_right hkpos h2
  have hle : (P : Subgroup H) ≤ Subgroup.normalizer (P : Set H) := by
    rw [← Sylow.coe_coe]
    exact Subgroup.le_normalizer
  have hself : Subgroup.normalizer (P : Set H) = (P : Subgroup H) :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hncard, hPcard])).symm
  -- `P` is commutative, so `N(P) = P ≤ C(P)`; apply Burnside's transfer theorem
  haveI : IsCyclic (P : Subgroup H) := isCyclic_of_prime_card hPcard
  haveI : IsMulCommutative (P : Subgroup H) := by
    constructor
    constructor
    intro a b
    letI := IsCyclic.commGroup (α := (P : Subgroup H))
    exact mul_comm a b
  have hcent : Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H) := by
    rw [hself, ← Sylow.coe_coe]
    exact Subgroup.le_centralizer _
  refine ⟨(MonoidHom.transferSylow P hcent).ker, MonoidHom.normal_ker _, ?_⟩
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hcent
  have hmul := hcompl.card_mul
  rw [hPcard, hH] at hmul
  exact Nat.eq_of_mul_eq_mul_right hp.out.pos hmul

omit [Finite H] in
/-- The image of a subgroup of a subgroup under `Subgroup.subtype` has the
same cardinality. -/
private lemma card_map_subtype {N : Subgroup H} (R : Subgroup N) :
    Nat.card (R.map N.subtype) = Nat.card R :=
  (Nat.card_congr (Subgroup.equivMapOfInjective R N.subtype
    N.subtype_injective).toEquiv).symm

end SylowCount

/-! ### The number of Sylow 5-subgroups of a group of order 60 -/

/-- A group of order `60` has `1` or `6` Sylow `5`-subgroups. -/
theorem card_sylow_5_of_card_60 [Finite G] (hG : Nat.card G = 60) :
    Nat.card (Sylow 5 G) = 1 ∨ Nat.card (Sylow 5 G) = 6 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdvd : Nat.card (Sylow 5 G) ∣ 12 :=
    card_sylow_dvd_of_card_eq_mul (by rw [hG])
  have hmod := card_sylow_modEq_one 5 G
  have key : ∀ n ∈ Nat.divisors 12, n % 5 = 1 % 5 → n = 1 ∨ n = 6 := by decide
  exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod

/-! ### Simplicity when there are six Sylow 5-subgroups -/

section Simplicity

variable {H : Type*} [Group H] [Finite H]

/-- A group of order `30` has a normal subgroup of order `5`.

If `n₅ = 1` this is the unique Sylow `5`-subgroup.  If `n₅ = 6`, the Sylow
`5`-subgroup is self-normalizing, so Burnside's transfer theorem produces a
normal complement `K` of order `6`; the unique Sylow `3`-subgroup of `K` is
characteristic in `K`, hence normal in `H`; the quotient by it has order `10`,
whose unique Sylow `5`-subgroup pulls back to a normal subgroup of order `15`,
whose unique Sylow `5`-subgroup is characteristic, hence normal in `H`. -/
private lemma exists_normal_of_card_five_of_card_30 (hH : Nat.card H = 30) :
    ∃ R : Subgroup H, R.Normal ∧ Nat.card R = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h30 : Nat.card H = 6 * 5 := by rw [hH]
  have h56 : ¬ (5 : ℕ) ∣ 6 := by norm_num
  have h16 : Nat.card (Sylow 5 H) = 1 ∨ Nat.card (Sylow 5 H) = 6 := by
    have hdvd := card_sylow_dvd_of_card_eq_mul h30
    have hmod := card_sylow_modEq_one 5 H
    have key : ∀ n ∈ Nat.divisors 6, n % 5 = 1 % 5 → n = 1 ∨ n = 6 := by decide
    exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod
  rcases h16 with h1 | h6
  · obtain ⟨R, hchar, hcard⟩ := exists_char_of_card_sylow_eq_one h30 h56 h1
    haveI := hchar
    exact ⟨R, inferInstance, hcard⟩
  · -- Burnside: a normal complement `K` of order `6`
    obtain ⟨K, hKnorm, hKcard⟩ := exists_normal_complement_of_card_sylow_eq h30 h56 h6
    haveI := hKnorm
    -- the unique Sylow `3`-subgroup of `K` is characteristic in `K`
    have h63 : Nat.card K = 2 * 3 := by rw [hKcard]
    have h32 : ¬ (3 : ℕ) ∣ 2 := by norm_num
    have hn3 : Nat.card (Sylow 3 K) = 1 := by
      have hdvd := card_sylow_dvd_of_card_eq_mul h63
      have hmod := card_sylow_modEq_one 3 K
      have key : ∀ n ∈ Nat.divisors 2, n % 3 = 1 % 3 → n = 1 := by decide
      exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod
    obtain ⟨Q', hQ'char, hQ'card⟩ := exists_char_of_card_sylow_eq_one h63 h32 hn3
    haveI := hQ'char
    set Q : Subgroup H := Q'.map K.subtype with hQdef
    haveI hQnorm : Q.Normal := by rw [hQdef]; infer_instance
    have hQcard : Nat.card Q = 3 := by rw [hQdef, card_map_subtype, hQ'card]
    -- the quotient `H ⧸ Q` has order `10`
    have hQidx : Q.index = 10 := by
      have hmi := Subgroup.card_mul_index Q
      rw [hQcard, hH] at hmi
      omega
    have hqcard : Nat.card (H ⧸ Q) = 2 * 5 := by
      rw [← Subgroup.index_eq_card, hQidx]
    -- its unique Sylow `5`-subgroup pulls back to a normal subgroup of order `15`
    have hn5q : Nat.card (Sylow 5 (H ⧸ Q)) = 1 := by
      have hdvd := card_sylow_dvd_of_card_eq_mul hqcard
      have hmod := card_sylow_modEq_one 5 (H ⧸ Q)
      have key : ∀ n ∈ Nat.divisors 2, n % 5 = 1 % 5 → n = 1 := by decide
      exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod
    obtain ⟨S, hSchar, hScard⟩ := exists_char_of_card_sylow_eq_one hqcard (by norm_num) hn5q
    haveI := hSchar
    set M : Subgroup H := S.comap (QuotientGroup.mk' Q) with hMdef
    haveI hMnorm : M.Normal := Subgroup.Normal.comap inferInstance _
    have hMcard : Nat.card M = 15 := by
      have hidxM : M.index = S.index := by
        rw [hMdef]
        exact Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective Q)
      have hmiS := Subgroup.card_mul_index S
      rw [hScard, hqcard] at hmiS
      have hSidx : S.index = 2 := by omega
      have hmiM := Subgroup.card_mul_index M
      rw [hH, hidxM, hSidx] at hmiM
      omega
    -- the unique Sylow `5`-subgroup of `M` is characteristic, hence normal in `H`
    have h153 : Nat.card M = 3 * 5 := by rw [hMcard]
    have hn5M : Nat.card (Sylow 5 M) = 1 := by
      have hdvd := card_sylow_dvd_of_card_eq_mul h153
      have hmod := card_sylow_modEq_one 5 M
      have key : ∀ n ∈ Nat.divisors 3, n % 5 = 1 % 5 → n = 1 := by decide
      exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod
    obtain ⟨R', hR'char, hR'card⟩ := exists_char_of_card_sylow_eq_one h153 (by norm_num) hn5M
    haveI := hR'char
    refine ⟨R'.map M.subtype, inferInstance, ?_⟩
    rw [card_map_subtype, hR'card]

/-- In a group of order `60` with six Sylow `5`-subgroups, a normal subgroup
whose order is divisible by `5` has order `30` or `60`: it contains every
Sylow `5`-subgroup. -/
private lemma card_eq_30_or_60_of_normal_of_five_dvd [Finite G] (hG : Nat.card G = 60)
    (h6 : Nat.card (Sylow 5 G) = 6) {N : Subgroup G} (hN : N.Normal)
    (h5 : 5 ∣ Nat.card N) : Nat.card N = 30 ∨ Nat.card N = 60 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdvd60 : Nat.card N ∣ 60 := hG ▸ Subgroup.card_subgroup_dvd_card N
  obtain ⟨k, hk⟩ := h5
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      exact absurd hk Nat.card_pos.ne'
    · exact h
  have h5k : ¬ 5 ∣ k := by
    rintro ⟨m, hm⟩
    have h25 : (25 : ℕ) ∣ 60 := by
      refine dvd_trans ⟨m, ?_⟩ hdvd60
      rw [hk, hm]; ring
    norm_num at h25
  have hcardN : Nat.card N = k * 5 := by rw [hk]; ring
  -- a Sylow `5`-subgroup of `N`, viewed as a Sylow `5`-subgroup of `G`
  obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow 5 N))
  have hQcard : Nat.card (Q : Subgroup N) = 5 := card_sylow_subgroup_eq_prime hcardN h5k Q
  have hQ₀card : Nat.card ((Q : Subgroup N).map N.subtype) = 5 := by
    rw [card_map_subtype, hQcard]
  have hfact60 : (Nat.card G).factorization 5 = 1 := by
    rw [hG, show (60 : ℕ) = 12 * 5 by norm_num]
    exact factorization_mul_self (by norm_num) (by norm_num)
  set Q₀ : Sylow 5 G := Sylow.ofCard ((Q : Subgroup N).map N.subtype)
    (by rw [hQ₀card, hfact60, pow_one]) with hQ₀def
  have hQ₀le : (Q₀ : Subgroup G) ≤ N := by
    rw [hQ₀def, Sylow.coe_ofCard]
    exact Subgroup.map_subtype_le _
  -- every Sylow `5`-subgroup of `G` lies inside `N`
  have hall : ∀ P : Sylow 5 G, (P : Subgroup G) ≤ N := by
    intro P
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q₀ P
    rw [← hg]
    intro x hx
    have hx' : (MulAut.conj g)⁻¹ x ∈ (Q₀ : Subgroup G) := by
      have hxs : x ∈ MulAut.conj g • (Q₀ : Subgroup G) := by
        rwa [← Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mp hxs
    have hxN : (MulAut.conj g)⁻¹ x ∈ N := hQ₀le hx'
    have hconj := hN.conj_mem _ hxN g
    have hval : g * ((MulAut.conj g)⁻¹ x) * g⁻¹ = x := by
      rw [MulAut.conj_inv_apply]; group
    rwa [hval] at hconj
  -- so `Sylow 5 G` injects into `Sylow 5 N`
  have hinj : Function.Injective (fun P : Sylow 5 G => P.subtype (hall P)) :=
    fun P₁ P₂ h => Sylow.subtype_injective h
  have hle6 : 6 ≤ Nat.card (Sylow 5 N) := by
    rw [← h6]
    exact Nat.card_le_card_of_injective _ hinj
  have hdvdk : Nat.card (Sylow 5 N) ∣ k := card_sylow_dvd_of_card_eq_mul hcardN
  have hk6 : 6 ≤ k := le_trans hle6 (Nat.le_of_dvd hkpos hdvdk)
  have hkdvd12 : k ∣ 12 := by
    have h512 : (5 : ℕ) * k ∣ 5 * 12 := by
      rw [← hk]
      exact hdvd60.trans (by norm_num)
    exact (mul_dvd_mul_iff_left (by norm_num : (5 : ℕ) ≠ 0)).mp h512
  have hk12 : k = 6 ∨ k = 12 := by
    have key : ∀ n ∈ Nat.divisors 12, 6 ≤ n → n = 6 ∨ n = 12 := by decide
    exact key _ (Nat.mem_divisors.mpr ⟨hkdvd12, by norm_num⟩) hk6
  rcases hk12 with h | h
  · left; rw [hk, h]
  · right; rw [hk, h]

/-- In a group of order `60` with six Sylow `5`-subgroups, there is no normal
subgroup of order `2`, `3` or `4`: the quotient (of order `30`, `20` or `15`)
would have a normal subgroup of order `5`, pulling back to a normal subgroup
of order `10`, `15` or `20`, which contradicts
`card_eq_30_or_60_of_normal_of_five_dvd`. -/
private lemma no_normal_of_card_234 [Finite G] (hG : Nat.card G = 60)
    (h6 : Nat.card (Sylow 5 G) = 6) {N : Subgroup G} (hN : N.Normal)
    (hcard : Nat.card N = 2 ∨ Nat.card N = 3 ∨ Nat.card N = 4) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI := hN
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hidx : Nat.card N * N.index = 60 := by rw [Subgroup.card_mul_index, hG]
  have hqcard : Nat.card (G ⧸ N) = N.index := (Subgroup.index_eq_card N).symm
  -- a normal subgroup of order `5` in the quotient
  have hS : ∃ S : Subgroup (G ⧸ N), S.Normal ∧ Nat.card S = 5 := by
    rcases hcard with h2 | h3 | h4
    · -- quotient of order 30
      have h30 : Nat.card (G ⧸ N) = 30 := by
        rw [h2] at hidx; rw [hqcard]; omega
      exact exists_normal_of_card_five_of_card_30 h30
    · -- quotient of order 20 = 4 * 5
      have h20 : Nat.card (G ⧸ N) = 4 * 5 := by
        rw [h3] at hidx; rw [hqcard]; omega
      have hn5 : Nat.card (Sylow 5 (G ⧸ N)) = 1 := by
        have hdvd := card_sylow_dvd_of_card_eq_mul h20
        have hmod := card_sylow_modEq_one 5 (G ⧸ N)
        have key : ∀ n ∈ Nat.divisors 4, n % 5 = 1 % 5 → n = 1 := by decide
        exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod
      obtain ⟨S, hchar, hcard5⟩ := exists_char_of_card_sylow_eq_one h20 (by norm_num) hn5
      haveI := hchar
      exact ⟨S, inferInstance, hcard5⟩
    · -- quotient of order 15 = 3 * 5
      have h15 : Nat.card (G ⧸ N) = 3 * 5 := by
        rw [h4] at hidx; rw [hqcard]; omega
      have hn5 : Nat.card (Sylow 5 (G ⧸ N)) = 1 := by
        have hdvd := card_sylow_dvd_of_card_eq_mul h15
        have hmod := card_sylow_modEq_one 5 (G ⧸ N)
        have key : ∀ n ∈ Nat.divisors 3, n % 5 = 1 % 5 → n = 1 := by decide
        exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod
      obtain ⟨S, hchar, hcard5⟩ := exists_char_of_card_sylow_eq_one h15 (by norm_num) hn5
      haveI := hchar
      exact ⟨S, inferInstance, hcard5⟩
  obtain ⟨S, hSnorm, hScard⟩ := hS
  -- pull back to a normal subgroup of `G` of order `5 * |N| ≤ 20`
  set M : Subgroup G := S.comap (QuotientGroup.mk' N) with hMdef
  have hMnorm : M.Normal := Subgroup.Normal.comap hSnorm _
  have hidxM : M.index = S.index := by
    rw [hMdef]
    exact Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)
  have hmiS := Subgroup.card_mul_index S
  rw [hScard, hqcard] at hmiS
  have hmiM := Subgroup.card_mul_index M
  rw [hG, hidxM] at hmiM
  -- compute `|M| = 5 * |N| ∈ {10, 15, 20}` and contradict the previous lemma
  have hMcard : Nat.card M = 5 * Nat.card N := by
    rcases hcard with h | h | h
    · rw [h] at hidx
      have h1 : N.index = 30 := by omega
      rw [h1] at hmiS
      have h2 : S.index = 6 := by omega
      rw [h2] at hmiM
      rw [h]; omega
    · rw [h] at hidx
      have h1 : N.index = 20 := by omega
      rw [h1] at hmiS
      have h2 : S.index = 4 := by omega
      rw [h2] at hmiM
      rw [h]; omega
    · rw [h] at hidx
      have h1 : N.index = 15 := by omega
      rw [h1] at hmiS
      have h2 : S.index = 3 := by omega
      rw [h2] at hmiM
      rw [h]; omega
  have h5M : 5 ∣ Nat.card M := ⟨Nat.card N, hMcard⟩
  have h3060 := card_eq_30_or_60_of_normal_of_five_dvd hG h6 hMnorm h5M
  rw [hMcard] at h3060
  rcases hcard with h | h | h <;> rw [h] at h3060 <;> omega

/-- A group of order `60` with six Sylow `5`-subgroups is simple. -/
theorem isSimpleGroup_of_card_60_of_card_sylow_5_eq_six [Finite G]
    (hG : Nat.card G = 60) (h6 : Nat.card (Sylow 5 G) = 6) :
    IsSimpleGroup G := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by rw [hG]; norm_num)
  refine ⟨fun N hN => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hNbot, hNtop⟩ := hcon
  haveI := hN
  have hdvd60 : Nat.card N ∣ 60 := hG ▸ Subgroup.card_subgroup_dvd_card N
  have hne1 : Nat.card N ≠ 1 := fun h => hNbot (Subgroup.card_eq_one.mp h)
  have hne60 : Nat.card N ≠ 60 := fun h =>
    hNtop (Subgroup.eq_top_of_card_eq _ (by rw [h, hG]))
  by_cases h5 : 5 ∣ Nat.card N
  · -- `|N| ∈ {30, 60}`; and `60` is excluded, so `|N| = 30`
    rcases card_eq_30_or_60_of_normal_of_five_dvd hG h6 hN h5 with h30 | h60
    · -- a normal subgroup of order `5` of `N` is its unique Sylow `5`-subgroup,
      -- hence characteristic in `N`, hence normal in `G` — contradicting `n₅ = 6`
      obtain ⟨R, hRnorm, hRcard⟩ := exists_normal_of_card_five_of_card_30 h30
      have hfact30 : (Nat.card N).factorization 5 = 1 := by
        rw [h30, show (30 : ℕ) = 6 * 5 by norm_num]
        exact factorization_mul_self (by norm_num) (by norm_num)
      set RSyl : Sylow 5 N := Sylow.ofCard R (by rw [hRcard, hfact30, pow_one])
        with hRSyl
      have hRSylnorm : (RSyl : Subgroup N).Normal := by
        rw [hRSyl, Sylow.coe_ofCard]; exact hRnorm
      haveI hRchar : R.Characteristic := by
        have := Sylow.characteristic_of_normal RSyl hRSylnorm
        rwa [hRSyl, Sylow.coe_ofCard] at this
      -- `R.map N.subtype` is a normal Sylow `5`-subgroup of `G`
      have hR₀card : Nat.card (R.map N.subtype) = 5 := by
        rw [card_map_subtype, hRcard]
      have hfact60 : (Nat.card G).factorization 5 = 1 := by
        rw [hG, show (60 : ℕ) = 12 * 5 by norm_num]
        exact factorization_mul_self (by norm_num) (by norm_num)
      set R₀Syl : Sylow 5 G := Sylow.ofCard (R.map N.subtype)
        (by rw [hR₀card, hfact60, pow_one]) with hR₀Syl
      have hR₀norm : (R₀Syl : Subgroup G).Normal := by
        rw [hR₀Syl, Sylow.coe_ofCard]; infer_instance
      haveI := Sylow.unique_of_normal R₀Syl hR₀norm
      have h1 : Nat.card (Sylow 5 G) = 1 := Nat.card_unique
      omega
    · exact hne60 h60
  · -- `|N| ∈ {2, 3, 4, 6, 12}`
    have hmem : Nat.card N = 2 ∨ Nat.card N = 3 ∨ Nat.card N = 4 ∨
        Nat.card N = 6 ∨ Nat.card N = 12 := by
      have key : ∀ n ∈ Nat.divisors 60, ¬ 5 ∣ n → n ≠ 1 →
          n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 12 := by decide
      exact key _ (Nat.mem_divisors.mpr ⟨hdvd60, by norm_num⟩) h5 hne1
    rcases hmem with h | h | h | h6' | h12
    · exact no_normal_of_card_234 hG h6 hN (Or.inl h)
    · exact no_normal_of_card_234 hG h6 hN (Or.inr (Or.inl h))
    · exact no_normal_of_card_234 hG h6 hN (Or.inr (Or.inr h))
    · -- `|N| = 6`: the unique Sylow `3`-subgroup of `N` is characteristic,
      -- giving a normal subgroup of `G` of order `3`
      have h623 : Nat.card N = 2 * 3 := by rw [h6']
      have hn3 : Nat.card (Sylow 3 N) = 1 := by
        have hdvd := card_sylow_dvd_of_card_eq_mul h623
        have hmod := card_sylow_modEq_one 3 N
        have key : ∀ n ∈ Nat.divisors 2, n % 3 = 1 % 3 → n = 1 := by decide
        exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod
      obtain ⟨Q', hchar, hcard3⟩ := exists_char_of_card_sylow_eq_one h623 (by norm_num) hn3
      haveI := hchar
      have hQnorm : (Q'.map N.subtype).Normal := inferInstance
      have hQcard : Nat.card (Q'.map N.subtype) = 3 := by
        rw [card_map_subtype, hcard3]
      exact no_normal_of_card_234 hG h6 hQnorm (Or.inr (Or.inl hQcard))
    · -- `|N| = 12`: either the Sylow `3`-subgroup of `N` is unique
      -- (characteristic of order `3`) or there are four of them, in which case
      -- Burnside gives a normal (Sylow `2`-)complement of order `4`,
      -- characteristic in `N`
      have h1243 : Nat.card N = 4 * 3 := by rw [h12]
      have hn3 : Nat.card (Sylow 3 N) = 1 ∨ Nat.card (Sylow 3 N) = 4 := by
        have hdvd := card_sylow_dvd_of_card_eq_mul h1243
        have hmod := card_sylow_modEq_one 3 N
        have key : ∀ n ∈ Nat.divisors 4, n % 3 = 1 % 3 → n = 1 ∨ n = 4 := by decide
        exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod
      rcases hn3 with h1 | h4
      · obtain ⟨Q', hchar, hcard3⟩ := exists_char_of_card_sylow_eq_one h1243 (by norm_num) h1
        haveI := hchar
        have hQnorm : (Q'.map N.subtype).Normal := inferInstance
        have hQcard : Nat.card (Q'.map N.subtype) = 3 := by
          rw [card_map_subtype, hcard3]
        exact no_normal_of_card_234 hG h6 hQnorm (Or.inr (Or.inl hQcard))
      · -- Burnside: normal complement of order `4`, which is the unique
        -- Sylow `2`-subgroup of `N`, hence characteristic
        obtain ⟨K, hKnorm, hKcard⟩ :=
          exists_normal_complement_of_card_sylow_eq h1243 (by norm_num) h4
        have hfact12 : (Nat.card N).factorization 2 = 2 := by
          rw [h12, show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
            Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
            Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
            Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
        set KSyl : Sylow 2 N := Sylow.ofCard K (by rw [hKcard, hfact12]; norm_num)
          with hKSyl
        have hKSylnorm : (KSyl : Subgroup N).Normal := by
          rw [hKSyl, Sylow.coe_ofCard]; exact hKnorm
        haveI hKchar : K.Characteristic := by
          have := Sylow.characteristic_of_normal KSyl hKSylnorm
          rwa [hKSyl, Sylow.coe_ofCard] at this
        have hKnorm' : (K.map N.subtype).Normal := inferInstance
        have hKcard' : Nat.card (K.map N.subtype) = 4 := by
          rw [card_map_subtype, hKcard]
        exact no_normal_of_card_234 hG h6 hKnorm' (Or.inr (Or.inr hKcard'))

end Simplicity

/-! ### Identification with the alternating group `A₅`

Following the classical argument: the conjugation action on the six Sylow
`5`-subgroups embeds `G` into `S₆`; since `G` is simple the image lies in
`A₆`.  The coset action of `A₆` on the six cosets of the image is again
faithful and lands in the alternating group, giving an automorphism-like
identification `A₆ ≃* A₆` carrying the image of `G` onto the stabilizer of a
point, which is `A₅`. -/

section AlternatingA5

open Equiv Equiv.Perm

/-- For a finite simple group of order `> 2`, every homomorphism to a
permutation group has image inside the alternating group (the sign character
must be trivial). -/
private lemma sign_eq_one_of_isSimpleGroup {H X : Type*} [Group H] [Finite H]
    [IsSimpleGroup H] [Fintype X] [DecidableEq X]
    (h2 : 2 < Nat.card H) (f : H →* Equiv.Perm X) (h : H) :
    Equiv.Perm.sign (f h) = 1 := by
  set s : H →* ℤˣ := Equiv.Perm.sign.comp f with hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal s.ker s.normal_ker with hbot | htop
  · exfalso
    have hinj : Function.Injective s := (MonoidHom.ker_eq_bot_iff s).mp hbot
    have hcard := Nat.card_le_card_of_injective s hinj
    have hunits : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
    omega
  · have hh : h ∈ s.ker := htop ▸ Subgroup.mem_top h
    simpa [hs] using hh

/-- A homomorphism out of a simple group whose kernel is not everything is
injective. -/
private lemma injective_of_ker_ne_top {H X : Type*} [Group H] [IsSimpleGroup H]
    [Group X] (f : H →* X) (hne : f.ker ≠ ⊤) : Function.Injective f := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker f.normal_ker with hbot | htop
  · exact (MonoidHom.ker_eq_bot_iff f).mp hbot
  · exact absurd htop hne

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The permutations in the alternating group fixing a given point, as a
subgroup of the alternating group. -/
private def altStabilizer (a : α) : Subgroup (alternatingGroup α) :=
  (MulAction.stabilizer (Equiv.Perm α) a).comap (alternatingGroup α).subtype

private lemma mem_altStabilizer {a : α} {σ : alternatingGroup α} :
    σ ∈ altStabilizer a ↔ (σ : Equiv.Perm α) a = a := by
  rw [altStabilizer, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  rfl

/-- Extension by the identity maps the alternating group of `{x // x ≠ a}`
into the stabilizer of `a` in the alternating group of `α`. -/
private def altStabilizerHom (a : α) :
    alternatingGroup {x : α // x ≠ a} →* altStabilizer a :=
  MonoidHom.codRestrict
    (MonoidHom.codRestrict
      (Equiv.Perm.ofSubtype.comp (alternatingGroup {x : α // x ≠ a}).subtype)
      (alternatingGroup α)
      (fun τ => Equiv.Perm.mem_alternatingGroup.mpr (by
        rw [MonoidHom.comp_apply, Equiv.Perm.sign_ofSubtype]
        exact Equiv.Perm.mem_alternatingGroup.mp τ.2)))
    (altStabilizer a)
    (fun τ => mem_altStabilizer.mpr
      (Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp)))

private lemma altStabilizerHom_bijective (a : α) :
    Function.Bijective (altStabilizerHom a) := by
  constructor
  · -- injectivity: recover the restriction from the extension pointwise
    intro τ τ' h
    have h1 : Equiv.Perm.ofSubtype (τ : Equiv.Perm {x : α // x ≠ a}) =
        Equiv.Perm.ofSubtype (τ' : Equiv.Perm {x : α // x ≠ a}) :=
      congrArg (fun σ : altStabilizer a => ((σ : alternatingGroup α) : Equiv.Perm α)) h
    have h2 : ∀ x : {x : α // x ≠ a},
        (τ : Equiv.Perm {x : α // x ≠ a}) x = (τ' : Equiv.Perm {x : α // x ≠ a}) x := by
      intro x
      have hx := congrArg (fun f : Equiv.Perm α => f (x : α)) h1
      rw [Equiv.Perm.ofSubtype_apply_coe, Equiv.Perm.ofSubtype_apply_coe] at hx
      exact Subtype.coe_injective hx
    exact Subtype.ext (Equiv.ext h2)
  · -- surjectivity: restrict a stabilizing permutation to `{x // x ≠ a}`
    rintro ⟨σ, hσ⟩
    have hfix : (σ : Equiv.Perm α) a = a := mem_altStabilizer.mp hσ
    have h₁ : ∀ x : α, ((σ : Equiv.Perm α) x ≠ a) ↔ (x ≠ a) := by
      intro x
      constructor
      · intro hx hxa
        exact hx (by rw [hxa, hfix])
      · intro hx hcon
        exact hx ((σ : Equiv.Perm α).injective (hcon.trans hfix.symm))
    have h₂ : ∀ x : α, (σ : Equiv.Perm α) x ≠ x → x ≠ a := by
      intro x hmoved hxa
      exact hmoved (by rw [hxa, hfix])
    refine ⟨⟨(σ : Equiv.Perm α).subtypePerm h₁, ?_⟩, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup,
        Equiv.Perm.sign_subtypePerm _ h₁ h₂]
      exact Equiv.Perm.mem_alternatingGroup.mp σ.2
    · apply Subtype.ext
      apply Subtype.ext
      exact Equiv.Perm.ofSubtype_subtypePerm h₁ h₂

/-- The stabilizer of a point in the alternating group is isomorphic to the
alternating group on the complement of that point. -/
private noncomputable def altStabilizerMulEquiv (a : α) :
    altStabilizer a ≃* alternatingGroup {x : α // x ≠ a} :=
  (MulEquiv.ofBijective _ (altStabilizerHom_bijective a)).symm

/-- **A group of order `60` with six Sylow `5`-subgroups is isomorphic to
`A₅`.**  The conjugation action on the Sylow `5`-subgroups embeds `G` in
`A₆`; the coset action of `A₆` on the six cosets of the image identifies the
image with a point stabilizer, which is `A₅`. -/
theorem mulEquiv_alternatingGroup_of_card_60_of_card_sylow_5_eq_six [Finite G]
    (hG : Nat.card G = 60) (h6 : Nat.card (Sylow 5 G) = 6) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : IsSimpleGroup G := isSimpleGroup_of_card_60_of_card_sylow_5_eq_six hG h6
  -- Step 1: the conjugation action on the six Sylow 5-subgroups, transported
  -- to `Fin 6`
  haveI : Fintype (Sylow 5 G) := Fintype.ofFinite _
  have hcard6 : Fintype.card (Sylow 5 G) = 6 := by
    rw [← Nat.card_eq_fintype_card, h6]
  let e : Sylow 5 G ≃ Fin 6 := Fintype.equivFinOfCardEq hcard6
  let φ₀ : G →* Equiv.Perm (Sylow 5 G) := MulAction.toPermHom G (Sylow 5 G)
  let φ : G →* Equiv.Perm (Fin 6) := (e.permCongrHom).toMonoidHom.comp φ₀
  -- the kernel of `φ` is not everything: otherwise every Sylow 5-subgroup
  -- would be normal, contradicting `n₅ = 6`
  have hker : φ.ker ≠ ⊤ := by
    intro htop
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 5 G))
    have hfix : ∀ g : G, g • P = P := by
      intro g
      have hg : g ∈ φ.ker := htop ▸ Subgroup.mem_top g
      have hg1 : e.permCongrHom (φ₀ g) = 1 := hg
      have hg0 : φ₀ g = 1 := by
        apply e.permCongrHom.injective
        rw [map_one]
        exact hg1
      have := congrArg (fun π : Equiv.Perm (Sylow 5 G) => π P) hg0
      simpa [φ₀, MulAction.toPermHom_apply] using this
    have hnorm : Subgroup.normalizer (P : Set G) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro g
      exact Sylow.smul_eq_iff_mem_normalizer.mp (hfix g)
    have hidx := Sylow.card_eq_index_normalizer P
    rw [hnorm, Subgroup.index_top] at hidx
    omega
  have hφinj : Function.Injective φ := injective_of_ker_ne_top φ hker
  -- `φ` lands in the alternating group
  have hsign : ∀ g, Equiv.Perm.sign (φ g) = 1 :=
    sign_eq_one_of_isSimpleGroup (by rw [hG]; norm_num) φ
  let ψ : G →* alternatingGroup (Fin 6) :=
    φ.codRestrict (alternatingGroup (Fin 6)) fun g =>
      Equiv.Perm.mem_alternatingGroup.mpr (hsign g)
  have hψinj : Function.Injective ψ := fun x y h =>
    hφinj (congrArg Subtype.val h)
  -- `G` is isomorphic to its image `H₁ ≤ A₆`, of index 6
  set H₁ : Subgroup (alternatingGroup (Fin 6)) := ψ.range with hH₁def
  let e₁ : G ≃* H₁ := MonoidHom.ofInjective hψinj
  have hH₁card : Nat.card H₁ = 60 := by
    rw [← hG]
    exact (Nat.card_congr e₁.toEquiv).symm
  have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  -- Step 2: the coset action of `A₆` on `A₆ ⧸ H₁`, transported to `Fin 6`
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp [Nat.card_eq_fintype_card])
  haveI : Fintype (alternatingGroup (Fin 6) ⧸ H₁) := Fintype.ofFinite _
  have hXcard : Fintype.card (alternatingGroup (Fin 6) ⧸ H₁) = 6 := by
    have hidx : H₁.index = 6 := by
      have hmi := Subgroup.card_mul_index H₁
      rw [hH₁card, hA6card] at hmi
      omega
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hidx]
  let e₂ : (alternatingGroup (Fin 6) ⧸ H₁) ≃ Fin 6 := Fintype.equivFinOfCardEq hXcard
  let χ₀ := MulAction.toPermHom (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6) ⧸ H₁)
  let χ : alternatingGroup (Fin 6) →* Equiv.Perm (Fin 6) :=
    (e₂.permCongrHom).toMonoidHom.comp χ₀
  set q₁ : alternatingGroup (Fin 6) ⧸ H₁ :=
    ((1 : alternatingGroup (Fin 6)) : alternatingGroup (Fin 6) ⧸ H₁) with hq₁
  -- membership in `H₁` is stabilizing the coset `q₁`
  have hstabmem : ∀ b : alternatingGroup (Fin 6), b ∈ H₁ ↔ b • q₁ = q₁ := by
    intro b
    conv_lhs => rw [← MulAction.stabilizer_quotient H₁]
    exact Iff.rfl
  -- value of `χ` at the marked point
  set x₀ : Fin 6 := e₂ q₁ with hx₀
  have hval : ∀ b : alternatingGroup (Fin 6), (χ b) x₀ = e₂ (b • q₁) := by
    intro b
    change (e₂.permCongr (χ₀ b)) (e₂ q₁) = e₂ (b • q₁)
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rfl
  -- the kernel of `χ` is not everything: otherwise `H₁ = ⊤`
  have hχker : χ.ker ≠ ⊤ := by
    intro htop
    have hH₁top : H₁ = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro b
      have hb : b ∈ χ.ker := htop ▸ Subgroup.mem_top b
      have hb1 : e₂.permCongrHom (χ₀ b) = 1 := hb
      have hb0 : χ₀ b = 1 := by
        apply e₂.permCongrHom.injective
        rw [map_one]
        exact hb1
      rw [hstabmem b]
      have := congrArg (fun π : Equiv.Perm (alternatingGroup (Fin 6) ⧸ H₁) => π q₁) hb0
      simpa [χ₀, MulAction.toPermHom_apply] using this
    rw [hH₁top, Subgroup.card_top, hA6card] at hH₁card
    omega
  have hχinj : Function.Injective χ := injective_of_ker_ne_top χ hχker
  have hχsign : ∀ b, Equiv.Perm.sign (χ b) = 1 :=
    sign_eq_one_of_isSimpleGroup (by rw [hA6card]; norm_num) χ
  -- the coset action gives a bijective endomorphism of `A₆`
  let ζ₀ : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6) :=
    χ.codRestrict (alternatingGroup (Fin 6)) fun b =>
      Equiv.Perm.mem_alternatingGroup.mpr (hχsign b)
  have hζinj : Function.Injective ζ₀ := fun x y h =>
    hχinj (congrArg Subtype.val h)
  have hζbij : Function.Bijective ζ₀ := Finite.injective_iff_bijective.mp hζinj
  let ζ : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6) :=
    MulEquiv.ofBijective ζ₀ hζbij
  -- Step 3: `ζ` carries `H₁` onto the stabilizer of `x₀`
  have hstab : ∀ b : alternatingGroup (Fin 6),
      b ∈ H₁ ↔ ((ζ₀ b : Equiv.Perm (Fin 6)) x₀ = x₀) := by
    intro b
    rw [hstabmem b]
    have hcoe : (ζ₀ b : Equiv.Perm (Fin 6)) = χ b := rfl
    rw [hcoe, hval b]
    constructor
    · intro hb; rw [hb]
    · intro hb; exact e₂.injective (by rw [hb])
  have himage : H₁.map ζ.toMonoidHom = altStabilizer x₀ := by
    ext τ
    rw [Subgroup.mem_map, mem_altStabilizer]
    constructor
    · rintro ⟨b, hbH, rfl⟩
      exact (hstab b).mp hbH
    · intro hτ
      obtain ⟨b, rfl⟩ := hζbij.2 τ
      exact ⟨b, (hstab b).mpr hτ, rfl⟩
  let e₃ : H₁ ≃* altStabilizer x₀ :=
    (ζ.subgroupMap H₁).trans (MulEquiv.subgroupCongr himage)
  -- Step 4: the stabilizer is `A₅`
  have hc5 : Fintype.card {x : Fin 6 // x ≠ x₀} = 5 := by
    simp [Fintype.card_subtype_compl]
  let e₅ : {x : Fin 6 // x ≠ x₀} ≃ Fin 5 := Fintype.equivFinOfCardEq hc5
  exact ⟨((e₁.trans e₃).trans (altStabilizerMulEquiv x₀)).trans e₅.altCongrHom⟩

end AlternatingA5

end Smallgroups.UsefulTheorems
