/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.CenterInvariant

/-!
# Center cardinality of non-abelian groups of order `p^4`

For a non-abelian group of order `p^4` (`p` prime), the center has order exactly `p` or `p^2`.
The possibilities `p^3` and `p^4` are ruled out:

* `|Z(G)| = p^4` would mean `Z(G) = G`, i.e. `G` is abelian.
* `|Z(G)| = p^3` would give `|G/Z(G)| = p`, a cyclic quotient, which forces `G` to be abelian
  by `comm_of_cyclic_center_quotient`.

This is the key structural input for the non-abelian classification of order `p^4`.
-/

namespace Smallgroups.UsefulTheorems

open Subgroup

variable {p : ℕ} [Fact p.Prime]

/-- In a non-abelian group of order `p^4`, the center has order `p` or `p^2`. -/
theorem center_card_eq_p_or_p_sq_of_nonabelian_p4 {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = p ^ 4) (hnonab : ¬ (∀ a b : G, a * b = b * a)) :
    Nat.card (center G) = p ∨ Nat.card (center G) = p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hG : IsPGroup p G := IsPGroup.of_card hcard
  have hGc : IsPGroup p (center G) := hG.to_subgroup _
  obtain ⟨k, hk_center⟩ := (IsPGroup.iff_card.mp hGc)
  -- hk_center : Nat.card (center G) = p ^ k
  have hk_le_4 : k ≤ 4 := by
    have hdv : Nat.card (center G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    rw [hk_center, hcard] at hdv
    rwa [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hdv
  have hk_ge_1 : 1 ≤ k := by
    haveI : Nontrivial (center G) :=
      center_nontrivial_of_card_prime_pow hcard (by norm_num : 0 < 4)
    have h_one_lt : 1 < Nat.card (center G) :=
      Finite.one_lt_card_iff_nontrivial.mpr (by infer_instance)
    rw [hk_center] at h_one_lt
    by_contra! h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at h_one_lt
    omega
  have hk_ne_4 : k ≠ 4 := by
    intro hk4
    subst hk4
    have htop : center G = ⊤ :=
      eq_top_of_card_eq _ (hk_center.trans hcard.symm)
    exact hnonab (center_eq_top_iff.mp htop)
  have hk_ne_3 : k ≠ 3 := by
    intro hk3
    subst hk3
    have hlag := card_mul_index (center G)
    rw [index_eq_card, hk_center, hcard] at hlag
    have hquot_card : Nat.card (G ⧸ center G) = p := by
      have : p ^ 3 * Nat.card (G ⧸ center G) = p ^ 3 * p := by
        rw [hlag]; ring
      exact mul_left_cancel₀ (pow_ne_zero 3 hp.ne_zero) this
    haveI : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card hquot_card
    have hcomm : ∀ a b : G, a * b = b * a := fun a b => comm_of_cyclic_center_quotient a b
    exact hnonab hcomm
  rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
  · exact Or.inl (by simpa using hk_center)
  · exact Or.inr (by simpa using hk_center)

end Smallgroups.UsefulTheorems
