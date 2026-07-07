/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Smallgroups.UsefulTheorems.CenterInvariant

/-!
# p-group generation: the central reduction step

This file starts the systematic *p-group generation* machinery used to classify groups of
prime-power order `p ^ n` for larger `n` (e.g. `32 = 2⁵` and `64 = 2⁶`).  The organizing
principle, following the p-group generation algorithm, is that every group `G` of order
`p ^ (n + 1)` is a **central extension**

  `1 → C_p → G → Q → 1`

of a group `Q` of order `p ^ n` by the cyclic group of order `p`: the center of a nontrivial
finite `p`-group is nontrivial, so it contains an element `z` of order `p` (Cauchy), and
`Z = ⟨z⟩` is a central — hence normal — subgroup with `|G ⧸ Z| = p ^ n`.

Downstream files rebuild `G` from `Q = G ⧸ Z` and a `2`-cocycle `Q → Q → ZMod p`
(`PGroupGeneration/CocycleGroup.lean`), turning the classification of order `p ^ (n + 1)`
into a finite problem over the (inductively known) groups of order `p ^ n`.

Main results:

* `normal_of_le_center` — subgroups of the center are normal;
* `exists_central_orderOf_eq_prime` — a central element of order `p` exists;
* `card_quotient_of_card_eq_prime` — `|G ⧸ Z| = p ^ n` when `|Z| = p`;
* `order_prime_pow_central_reduction` — the bundled reduction step.
-/

namespace Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- Any subgroup of the center is normal. -/
theorem normal_of_le_center {H : Subgroup G} (h : H ≤ Subgroup.center G) : H.Normal := by
  constructor
  intro x hx g
  have hg : g * x = x * g := (Subgroup.mem_center_iff.mp (h hx)) g
  rw [hg, mul_inv_cancel_right]
  exact hx

/-- **Cauchy in the center**: a group of order `p ^ (n + 1)` has a central element of
order `p`. -/
theorem exists_central_orderOf_eq_prime [Finite G] {p n : ℕ} [Fact p.Prime]
    (hG : Nat.card G = p ^ (n + 1)) :
    ∃ z : G, z ∈ Subgroup.center G ∧ orderOf z = p := by
  haveI : Nontrivial (Subgroup.center G) :=
    center_nontrivial_of_card_prime_pow hG (Nat.succ_pos n)
  have hdvd : p ∣ Nat.card (Subgroup.center G) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((IsPGroup.of_card hG).to_subgroup _)
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact absurd (hk.trans (pow_zero p))
        (Finite.one_lt_card (α := Subgroup.center G)).ne'
    · exact hk ▸ dvd_pow_self p hkpos.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) p hdvd
  exact ⟨(z : G), z.2, (orderOf_injective (Subgroup.center G).subtype
    (Subgroup.subtype_injective _) z).trans hz⟩

/-- The quotient by a subgroup of order `p` in a group of order `p ^ (n + 1)` has order
`p ^ n`. -/
theorem card_quotient_of_card_eq_prime [Finite G] {p n : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ (n + 1)) {Z : Subgroup G} (hZ : Nat.card Z = p) :
    Nat.card (G ⧸ Z) = p ^ n := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  rw [hZ, hG, pow_succ] at h
  exact (Nat.eq_of_mul_eq_mul_right hp.pos h).symm

/-- **The central reduction step**: a group of order `p ^ (n + 1)` has a central element `z`
of order `p` such that `⟨z⟩` is normal and `G ⧸ ⟨z⟩` has order `p ^ n`.  Hence `G` is a
central extension of a group of order `p ^ n` by `C_p`. -/
theorem order_prime_pow_central_reduction [Finite G] {p n : ℕ} [Fact p.Prime]
    (hG : Nat.card G = p ^ (n + 1)) :
    ∃ z : G, z ∈ Subgroup.center G ∧ orderOf z = p ∧
      (Subgroup.zpowers z).Normal ∧ Nat.card (G ⧸ Subgroup.zpowers z) = p ^ n := by
  obtain ⟨z, hzc, hzp⟩ := exists_central_orderOf_eq_prime hG
  have hle : Subgroup.zpowers z ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hzc
  exact ⟨z, hzc, hzp, normal_of_le_center hle,
    card_quotient_of_card_eq_prime Fact.out hG ((Nat.card_zpowers z).trans hzp)⟩

end Smallgroups.UsefulTheorems
