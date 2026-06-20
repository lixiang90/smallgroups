/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeOrderClassification
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Groups of order `p * q` with `q ∤ p - 1` are cyclic

Let `p > q` be distinct primes.  Sylow's theorems show the Sylow `p`-subgroup is always normal
(its count divides `q` and is `≡ 1 [MOD p]`, forcing it to be `1`).  The Sylow `q`-subgroup count
divides `p` and is `≡ 1 [MOD q]`, so it is `1` or `p`; it is `1` exactly when `q ∤ p - 1`.

When **both** Sylow subgroups are normal the group is nilpotent, and a nilpotent group whose order
is squarefree (a `Z`-group, all of whose Sylow subgroups are cyclic) is cyclic.  Hence:

* `isCyclic_of_card_eq_prime_mul` — if `p, q` are distinct primes, `q < p`, `q ∤ p - 1` and
  `Nat.card G = p * q`, then `G` is cyclic.

This is the "one isomorphism class" half of the classification of groups of order `p * q`.  (The
remaining case `q ∣ p - 1`, where a non-abelian semidirect product `ℤ/p ⋊ ℤ/q` also exists, is not
treated here.)
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-- For distinct primes `p > q` with `q ∤ p - 1`, **every Sylow subgroup of a group of order
`p * q` is normal**. -/
theorem sylow_normal_of_card_eq_prime_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hdvd : ¬ q ∣ p - 1) [Finite G] (hG : Nat.card G = p * q)
    {r : ℕ} [Fact r.Prime] (P : Sylow r G) : (↑P : Subgroup G).Normal := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  -- The Sylow `p`-count is `1`.
  have hnp : Nat.card (Sylow p G) = 1 := by
    obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
    have hpq : Nat.card (Sylow p G) ∣ p * q :=
      hG ▸ (P0.card_dvd_index.trans (Subgroup.index_dvd_card _))
    have hndvd : ¬ p ∣ Nat.card (Sylow p G) := not_dvd_card_sylow p G
    have hdq : Nat.card (Sylow p G) ∣ q :=
      Nat.Coprime.dvd_of_dvd_mul_left ((hp.coprime_iff_not_dvd.mpr hndvd).symm) hpq
    rcases (Nat.dvd_prime hq).mp hdq with h | h
    · exact h
    · exfalso
      have hmod := card_sylow_modEq_one p G
      rw [h] at hmod
      have hd : p ∣ q - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
      have := Nat.le_of_dvd (by omega) hd
      omega
  -- The Sylow `q`-count is `1` (this is where `q ∤ p - 1` is used).
  have hnq : Nat.card (Sylow q G) = 1 := by
    obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow q G))
    have hpq : Nat.card (Sylow q G) ∣ p * q :=
      hG ▸ (P0.card_dvd_index.trans (Subgroup.index_dvd_card _))
    have hndvd : ¬ q ∣ Nat.card (Sylow q G) := not_dvd_card_sylow q G
    have hdp : Nat.card (Sylow q G) ∣ p :=
      Nat.Coprime.dvd_of_dvd_mul_right ((hq.coprime_iff_not_dvd.mpr hndvd).symm) hpq
    rcases (Nat.dvd_prime hp).mp hdp with h | h
    · exact h
    · exfalso
      have hmod := card_sylow_modEq_one q G
      rw [h] at hmod
      exact hdvd ((Nat.modEq_iff_dvd' (by omega)).mp hmod.symm)
  -- Conclude normality for the given prime `r`.
  by_cases hrp : r = p
  · haveI : Subsingleton (Sylow r G) := by rw [hrp]; exact (Nat.card_eq_one_iff_unique.mp hnp).1
    exact normal_of_subsingleton P
  by_cases hrq : r = q
  · haveI : Subsingleton (Sylow r G) := by rw [hrq]; exact (Nat.card_eq_one_iff_unique.mp hnq).1
    exact normal_of_subsingleton P
  · -- `r ∤ p * q`, so the Sylow `r`-subgroup is trivial, hence normal.
    have hr : r.Prime := Fact.out
    have hrpq : ¬ r ∣ p * q := by
      intro h
      rcases hr.dvd_mul.mp h with h | h
      · exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp h)
      · exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)
    have hcardP : Nat.card (↑P : Subgroup G) = 1 := by
      rw [Sylow.card_eq_multiplicity, hG, Nat.factorization_eq_zero_of_not_dvd hrpq, pow_zero]
    have hbot : (↑P : Subgroup G) = ⊥ := Subgroup.eq_bot_of_card_eq (P : Subgroup G) hcardP
    rw [hbot]
    exact Subgroup.normal_bot

/-- **A group of order `p * q` with `p > q` distinct primes and `q ∤ p - 1` is cyclic.** -/
theorem isCyclic_of_card_eq_prime_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hdvd : ¬ q ∣ p - 1) (hG : Nat.card G = p * q) : IsCyclic G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [hG]; exact Nat.mul_ne_zero hp.pos.ne' hq.pos.ne')
  haveI : IsZGroup G := IsZGroup.of_squarefree (by
    rw [hG]
    exact (Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr (by omega))).mpr
      ⟨hp.squarefree, hq.squarefree⟩)
  haveI : Group.IsNilpotent G :=
    ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 3 rfl rfl).mpr
      (fun _ _ P => sylow_normal_of_card_eq_prime_mul hp hq hqp hdvd hG P)
  infer_instance

end Smallgroups.UsefulTheorems
