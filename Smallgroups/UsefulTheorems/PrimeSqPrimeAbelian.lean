/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeSqPrime
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.SemidirectProductClassify
import Smallgroups.UsefulTheorems.Counting
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Groups of order `p² q` with `p ∤ q − 1` and `q ∤ p² − 1` are abelian

Building on `PrimeSqPrime.lean`, which writes `G ≃* P ⋊[φ] K` (`P` the normal Sylow `p`-subgroup of
order `p²`, `K` of order `q`), this file shows that when additionally `q ∤ p² − 1`, the action `φ`
is trivial, so `G ≅ P × K` is **abelian**. There are then exactly **two** isomorphism classes:
`ℤ/p²q` and `ℤ/p × ℤ/pq`.

The key step is `aut_eq_one_of_card_psq`: an automorphism `α` of a group of order `p²` with
`α^q = 1` is the identity. Acting by the `q`-group `⟨α⟩`, the fixed points `{x | α x = x}` form a
subgroup whose order divides `p²` and is `≡ p² [MOD q]` (`IsPGroup.card_modEq_card_fixedPoints`);
were `α ≠ 1` this order would be `1` or `p`, forcing `q ∣ p² − 1`, contrary to hypothesis.
-/

namespace Smallgroups.UsefulTheorems

open scoped Pointwise

variable {G : Type*} [Group G]

/-- An automorphism `α` of a group of order `p²` with `α^q = 1` (where `q ∤ p² − 1`, `q ≠ p`) is the
identity. -/
theorem aut_eq_one_of_card_psq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hqdvd : ¬ q ∣ p ^ 2 - 1) {P : Type*} [Group P] [Finite P] (hP : Nat.card P = p ^ 2)
    (α : MulAut P) (hα : α ^ q = 1) : α = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- the cyclic `q`-group `H = ⟨α⟩`
  have hcardH : Nat.card (Subgroup.zpowers α) ∣ q := by
    rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hα
  obtain ⟨n, hn⟩ : ∃ n, Nat.card (Subgroup.zpowers α) = q ^ n := by
    rcases (Nat.dvd_prime hq).mp hcardH with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  haveI hHp : IsPGroup q (Subgroup.zpowers α) := IsPGroup.of_card hn
  -- the fixed points of `α` form a subgroup
  let F : Subgroup P :=
    { carrier := {x | α x = x}
      one_mem' := map_one α
      mul_mem' := fun ha hb => by simp only [Set.mem_setOf_eq] at *; rw [map_mul, ha, hb]
      inv_mem' := fun ha => by simp only [Set.mem_setOf_eq] at *; rw [map_inv, ha] }
  have hFset : MulAction.fixedPoints (Subgroup.zpowers α) P = (F : Set P) := by
    ext x
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨α, Subgroup.mem_zpowers α⟩
    · intro hx g
      have hαx : α x = x := hx
      have hstab : (g : MulAut P) ∈ MulAction.stabilizer (MulAut P) x :=
        Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (show α • x = x from hαx)) g.2
      exact MulAction.mem_stabilizer_iff.mp hstab
  -- `|F| ≡ p² [MOD q]` and `|F| ∣ p²`
  have hmod : p ^ 2 ≡ Nat.card F [MOD q] := by
    have h := hHp.card_modEq_card_fixedPoints P
    rw [hP] at h
    rwa [Nat.card_congr (Equiv.setCongr hFset)] at h
  have hdvd : Nat.card F ∣ p ^ 2 := hP ▸ Subgroup.card_subgroup_dvd_card F
  -- `q ∣ p − 1 → q ∣ p² − 1`, used to discharge the small-`F` cases
  have hstep : q ∣ p - 1 → False := fun hqp1 => by
    apply hqdvd
    have hp1 : p ≡ 1 [MOD q] := ((Nat.modEq_iff_dvd' hp.one_le).mpr hqp1).symm
    have hp2 : p ^ 2 ≡ 1 [MOD q] := by simpa using hp1.pow 2
    exact (Nat.modEq_iff_dvd' (by nlinarith [hp.two_le] : 1 ≤ p ^ 2)).mp hp2.symm
  -- classify `|F| ∈ {1, p, p²}`
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases k
  · -- `|F| = 1`: `p² ≡ 1 [MOD q]`, so `q ∣ p² − 1`
    exfalso; apply hqdvd
    rw [pow_zero] at hk
    rw [hk] at hmod
    exact (Nat.modEq_iff_dvd' (by nlinarith [hp.two_le] : 1 ≤ p ^ 2)).mp hmod.symm
  · -- `|F| = p`: `p² ≡ p [MOD q]`, cancel `p` to get `q ∣ p − 1`
    exfalso; apply hstep
    rw [pow_one] at hk
    rw [hk] at hmod
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hcancel : p ≡ 1 [MOD q] := by
      have h2 : p * p ≡ p * 1 [MOD q] := by rw [mul_one, ← pow_two]; exact hmod
      exact Nat.ModEq.cancel_left_of_coprime (by rwa [Nat.coprime_comm] at hcop) h2
    exact (Nat.modEq_iff_dvd' hp.one_le).mp hcancel.symm
  · -- `|F| = p²`: `F = ⊤`, so `α` fixes everything, i.e. `α = 1`
    have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hk, hP])
    ext x
    have hxF : x ∈ F := hFtop ▸ Subgroup.mem_top x
    exact hxF

/-! ### The CRT product isomorphism -/

/-- `ℤ/m × ℤ/n ≅ ℤ/mn` for coprime `m, n` (multiplicative). -/
noncomputable def crtProd (m n : ℕ) (h : Nat.Coprime m n) :
    Multiplicative (ZMod m) × Multiplicative (ZMod n) ≃* Multiplicative (ZMod (m * n)) :=
  (MulEquiv.prodMultiplicative (ZMod m) (ZMod n)).symm.trans
    (AddEquiv.toMultiplicative (ZMod.chineseRemainder h).symm.toAddEquiv)

/-! ### `G` is abelian, with exactly two isomorphism classes -/

/-- **Classification.** A group of order `p² q` with `p ∤ q − 1` and `q ∤ p² − 1` is isomorphic to
the cyclic group `ℤ/p²q` or to `ℤ/p × ℤ/pq`. -/
theorem psq_prime_abelian_classification {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpdvd : ¬ p ∣ q - 1) (hqdvd : ¬ q ∣ p ^ 2 - 1) [Finite G] (hG : Nat.card G = p ^ 2 * q) :
    Nonempty (G ≃* Multiplicative (ZMod (p ^ 2 * q))) ∨
      Nonempty (G ≃* Multiplicative (ZMod p) × Multiplicative (ZMod (p * q))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  obtain ⟨P, K, φ, _, hPcard, hKcard, ⟨e⟩⟩ := psq_semidirectProduct hp hq hpq hpdvd hG
  -- the action is trivial
  have hφ : φ = 1 := MonoidHom.ext fun k => by
    have hkq : k ^ q = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (hKcard ▸ orderOf_dvd_natCard k)
    have hαq : (φ k) ^ q = 1 := by rw [← map_pow, hkq, map_one]
    change φ k = 1
    exact aut_eq_one_of_card_psq hp hq hpq hqdvd hPcard (φ k) hαq
  -- so `G ≅ P × K`
  have e1 : G ≃* (↥P × ↥K) :=
    e.trans ((semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd)
  have eK : (↥K) ≃* Multiplicative (ZMod q) := (prime_classification hq hKcard).some
  rcases prime_sq_classification hPcard with hP | hP
  · -- `P ≅ ℤ/p²` → cyclic `ℤ/p²q`
    exact Or.inl ⟨e1.trans <| (MulEquiv.prodCongr hP.some eK).trans
      (crtProd (p ^ 2) q (hcop.pow_left 2))⟩
  · -- `P ≅ (ℤ/p)²` → `ℤ/p × ℤ/pq`
    exact Or.inr ⟨e1.trans <| (MulEquiv.prodCongr hP.some eK).trans <|
      MulEquiv.prodAssoc.trans
        (MulEquiv.prodCongr (MulEquiv.refl _) (crtProd p q hcop))⟩

/-- **A group of order `p² q` with `p ∤ q − 1` and `q ∤ p² − 1` is abelian.** -/
theorem psq_prime_abelian {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpdvd : ¬ p ∣ q - 1) (hqdvd : ¬ q ∣ p ^ 2 - 1) [Finite G] (hG : Nat.card G = p ^ 2 * q)
    (a b : G) : a * b = b * a := by
  rcases psq_prime_abelian_classification hp hq hpq hpdvd hqdvd hG with h | h
  · obtain ⟨e⟩ := h
    exact e.injective (by rw [map_mul, map_mul]; exact mul_comm (e a) (e b))
  · obtain ⟨e⟩ := h
    exact e.injective (by rw [map_mul, map_mul]; exact mul_comm (e a) (e b))

/-- **The two classes are distinct:** `ℤ/p²q` is cyclic, `ℤ/p × ℤ/pq` is not. -/
theorem psq_prime_distinct {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ¬ Nonempty (Multiplicative (ZMod (p ^ 2 * q)) ≃*
      (Multiplicative (ZMod p) × Multiplicative (ZMod (p * q)))) := by
  rintro ⟨e⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  haveI : IsCyclic (Multiplicative (ZMod p) × Multiplicative (ZMod (p * q))) :=
    isCyclic_of_surjective e e.surjective
  have hcop := coprime_card_of_isCyclic_prod
    (Multiplicative (ZMod p)) (Multiplicative (ZMod (p * q)))
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at hcop
  rw [Nat.coprime_mul_iff_right] at hcop
  exact absurd ((Nat.gcd_self p).symm.trans hcop.1) hp.one_lt.ne'

/-! ### Packaging the two classes -/

/-- `ℤ/p²q` (cyclic). -/
abbrev psqPrimeRep1 (p q : ℕ) : Type := Multiplicative (ZMod (p ^ 2 * q))
/-- `ℤ/p × ℤ/pq`. -/
abbrev psqPrimeRep2 (p q : ℕ) : Type := Multiplicative (ZMod p) × Multiplicative (ZMod (p * q))

theorem card_psqPrimeRep1 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Nat.card (psqPrimeRep1 p q) = p ^ 2 * q := by
  haveI : NeZero (p ^ 2 * q) := ⟨Nat.mul_ne_zero (pow_ne_zero 2 hp.ne_zero) hq.ne_zero⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem card_psqPrimeRep2 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    Nat.card (psqPrimeRep2 p q) = p ^ 2 * q := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, Fintype.card_multiplicative, ZMod.card, ZMod.card]; ring

/-- **The two abelian classes are a complete, non-redundant classification of order `p²q`** (for
`p ∤ q − 1`, `q ∤ p² − 1`). -/
theorem psq_prime_isClassif {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpdvd : ¬ p ∣ q - 1) (hqdvd : ¬ q ∣ p ^ 2 - 1) {N : ℕ} (hN : p ^ 2 * q = N) :
    IsClassif N (rep2 (psqPrimeRep1 p q) (psqPrimeRep2 p q)) := by
  subst hN
  refine isClassif_two (psqPrimeRep1 p q) (psqPrimeRep2 p q)
    (card_psqPrimeRep1 hp hq) (card_psqPrimeRep2 hp hq) (fun G _ hG => ?_)
    (psq_prime_distinct hp hq)
  haveI : Finite G := Nat.finite_of_card_ne_zero
    (by rw [hG]; exact Nat.mul_ne_zero (pow_ne_zero 2 hp.ne_zero) hq.ne_zero)
  exact psq_prime_abelian_classification hp hq hpq hpdvd hqdvd hG

end Smallgroups.UsefulTheorems
