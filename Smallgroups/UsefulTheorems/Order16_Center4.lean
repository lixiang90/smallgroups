/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Groups of order 16 with center ≅ C4

There are exactly **2** non-abelian groups of order 16 whose center is a cyclic group
of order 4: the modular maximal-cyclic group `C8 ⋊₅ C2` (defined as `order16_N1`)
and `Q8 ⋊ C2` (currently a placeholder `order16_N2`).

## Main results

* `order16_N1_classification` — a 16-group with center C4 and an element of order 8 is `order16_N1`
* `order16_N2_classification` — (future) a 16-group
with center C4 and no element of order 8 is `order16_N2`
-/

namespace Smallgroups.UsefulTheorems

open SemidirectProduct
open Subgroup
open scoped Pointwise

/-! ### Characterization of `order16_N1` (C8 ⋊₅ C2)

Among the two 16-groups with center C4, only `order16_N1` contains an element of order 8.
-/

/-- A group of order 16 with center ≅ C4 and containing an element of order 8 is isomorphic to
`order16_N1` (C8 ⋊₅ C2 via `x ↦ x⁵`). -/
theorem order16_N1_classification {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 16)
    (hcenter : Nonempty (center G ≃* CyclicRep 4))
    (hord8 : ∃ g : G, orderOf g = 8) :
    Nonempty (G ≃* order16_N1) := by
  rcases hord8 with ⟨g, hg⟩
  have hg8 : g ^ 8 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  let H : Subgroup G := Subgroup.zpowers g
  have hHcard : Nat.card H = 8 := by rw [Nat.card_zpowers, hg]
  have hHindex : H.index = 2 := by
    have hmul := H.card_mul_index; rw [hHcard, hcard] at hmul; omega
  haveI hHnorm : H.Normal := Subgroup.normal_of_index_eq_two hHindex
  have hZCcard : Nat.card (center G) = 4 := by
    rcases hcenter with ⟨hc⟩
    have hc4 : Nat.card (CyclicRep 4) = 4 := card_cyclicRep (by norm_num : 4 ≠ 0)
    rw [← hc4, ← Nat.card_congr hc.toEquiv]

  -- Proof strategy: show Z(G) = ⟨g²⟩ ≤ H, pick t ∉ H with t·g·t⁻¹ = g⁵,
  -- find s with s² = 1 and s·g·s⁻¹ = g⁵, then build isomorphism to C8 ⋊₅ C2.

  -- Step 1: Show Z(G) ≤ H, using the second isomorphism theorem
  haveI : Fintype G := Fintype.ofFinite G
  let Z : Subgroup G := center G
  have hZ_le_H : Z ≤ H := by
    have h_iso : Z ⧸ H.subgroupOf Z ≃* ((Z ⊔ H : Subgroup G) ⧸ H.subgroupOf (Z ⊔ H : Subgroup G)) :=
      QuotientGroup.quotientInfEquivProdNormalQuotient Z H
    have h_card_iso : Nat.card (Z ⧸ H.subgroupOf Z) =
        Nat.card ((Z ⊔ H : Subgroup G) ⧸ H.subgroupOf (Z ⊔ H : Subgroup G)) :=
      Nat.card_congr h_iso.toEquiv
    -- Left side: card * |Z∩H| = |Z| = 4
    have h_left : Nat.card (Z ⧸ H.subgroupOf Z) * Nat.card (H.subgroupOf Z) = 4 := by
      have h_mul := (H.subgroupOf Z).index_mul_card
      rw [Subgroup.index_eq_card, hZCcard] at h_mul; exact h_mul
    -- Right side: card * 8 = |Z ⊔ H|
    have hcard_Hsub : Nat.card (H.subgroupOf (Z ⊔ H : Subgroup G)) = 8 := by
      have hequiv : H.subgroupOf (Z ⊔ H : Subgroup G) ≃* H :=
        Subgroup.subgroupOfEquivOfLe (le_sup_right (a := Z) (b := H))
      rw [Nat.card_congr hequiv.toEquiv, hHcard]
    have h_right : Nat.card ((Z ⊔ H : Subgroup G) ⧸ H.subgroupOf (Z ⊔ H : Subgroup G)) * 8 =
        Nat.card (Z ⊔ H : Subgroup G) := by
      have h_mul := (H.subgroupOf (Z ⊔ H : Subgroup G)).index_mul_card
      rw [Subgroup.index_eq_card, hcard_Hsub] at h_mul
      exact h_mul
    set k := Nat.card (Z ⧸ H.subgroupOf Z) with hk_def
    have hk_left : k * Nat.card (H.subgroupOf Z) = 4 := h_left
    have hk_right : k * 8 = Nat.card (Z ⊔ H : Subgroup G) := by
      calc
        k * 8 = Nat.card ((Z ⊔ H : Subgroup G) ⧸ H.subgroupOf (Z ⊔ H : Subgroup G)) * 8 := by
          rw [h_card_iso]
        _ = Nat.card (Z ⊔ H : Subgroup G) := h_right
    -- k ≥ 1 (quotient has at least one element)
    have hk_pos : 0 < k := by dsimp [k]; exact Nat.card_pos
    have h_inter_pos : 0 < Nat.card (H.subgroupOf Z) := Nat.card_pos
    -- From k * 8 = |Z⊔H| ≤ |G| = 16, we have k ≤ 2
    have hsup_le_16 : Nat.card (Z ⊔ H : Subgroup G) ≤ 16 := by
      have hmul := (Z ⊔ H : Subgroup G).card_mul_index
      rw [hcard] at hmul
      -- Nat.card * index = 16, so Nat.card divides 16
      apply Nat.le_of_dvd (by norm_num)
      rw [← hmul]
      exact dvd_mul_right _ _
    have hk_le_2 : k ≤ 2 := by rw [← hk_right] at hsup_le_16; omega
    -- k ∈ {1, 2}.  If k = 1, then |Z∩H| = 4 = |Z|, so Z ≤ H.
    -- If k = 2, then |Z⊔H| = 16 = |G|, so Z⊔H = G, and G is abelian → contradiction.
    by_cases hk1 : k = 1
    · rw [hk1] at hk_left
      have h_inter_card4 : Nat.card (H.subgroupOf Z) = 4 := by omega
      have h_subgroupOf_eq_top : H.subgroupOf Z = ⊤ :=
        Subgroup.eq_top_of_card_eq (H.subgroupOf Z) (by rw [hZCcard, h_inter_card4])
      intro z hz
      have hz_top : (⟨z, hz⟩ : Z) ∈ H.subgroupOf Z := by
        rw [h_subgroupOf_eq_top]
        exact Subgroup.mem_top _
      have hzH : (z : G) ∈ H := by
        have hmem : (⟨z, hz⟩ : Z) ∈ (H.subgroupOf Z) := by
          rw [h_subgroupOf_eq_top]
          exact Subgroup.mem_top _
        rw [Subgroup.mem_subgroupOf] at hmem
        simpa using hmem
      exact hzH
    · have hk2 : k = 2 := by omega
      rw [hk2] at hk_right
      have hsup_card16 : Nat.card (Z ⊔ H : Subgroup G) = 16 := by omega
      have hsup_eq_top : Z ⊔ H = ⊤ :=
        Subgroup.eq_top_of_card_eq (Z ⊔ H : Subgroup G) (by rw [hsup_card16, hcard])
      -- G = Z·H.  Z is central, H is abelian, so G is abelian → |Z(G)| = 16, contradiction
      have h_mul_set : ((⊤ : Subgroup G) : Set G) = (Z : Set G) * (H : Set G) := by
        have h := mul_normal Z H
        simpa [hsup_eq_top] using h
      have hZ_comm (z : Z) (x : G) : (z : G) * x = x * (z : G) := by
        rcases z with ⟨z, hz⟩; rw [Subgroup.mem_center_iff] at hz; exact (hz x).symm
      have hH_comm_val (x y : H) : (x : G) * (y : G) = (y : G) * (x : G) := by
        rcases Subgroup.mem_zpowers_iff.mp x.2 with ⟨m, hm⟩
        rcases Subgroup.mem_zpowers_iff.mp y.2 with ⟨n, hn⟩
        calc
          ((x : G) * (y : G)) = (g ^ m) * (g ^ n) := by rw [hm, hn]
          _ = (g ^ n) * (g ^ m) := ((Commute.refl g).zpow_zpow m n).eq
          _ = ((y : G) * (x : G)) := by rw [hn, hm]
      have hab : ∀ a b : G, a * b = b * a := by
        intro a b
        have ha : a ∈ ((Z : Set G) * (H : Set G)) := by rw [← h_mul_set]; exact Subgroup.mem_top a
        have hb : b ∈ ((Z : Set G) * (H : Set G)) := by rw [← h_mul_set]; exact Subgroup.mem_top b
        rcases ha with ⟨za, haZ, haH, haHmem, ha_eq⟩
        rcases hb with ⟨zb, hbZ, hbH, hbHmem, hb_eq⟩
        have ha_eq' : a = za * haH := ha_eq.symm
        have hb_eq' : b = zb * hbH := hb_eq.symm
        rw [ha_eq', hb_eq']
        calc
          (za * haH) * (zb * hbH) = za * (haH * zb) * hbH := by group
          _ = za * (zb * haH) * hbH := by rw [hZ_comm ⟨zb, hbZ⟩ haH]
          _ = (za * zb) * (haH * hbH) := by group
          _ = (zb * za) * (hbH * haH) := by
            rw [hZ_comm ⟨za, haZ⟩ zb, hH_comm_val ⟨haH, haHmem⟩ ⟨hbH, hbHmem⟩]
          _ = zb * (za * hbH) * haH := by group
          _ = (zb * hbH) * (za * haH) := by rw [hZ_comm ⟨za, haZ⟩ hbH]; group
      have hZCcard16 : Nat.card (center G) = 16 := by
        have h' := card_center_eq_card_of_comm G hab
        rw [hcard] at h'
        exact h'
      rw [hZCcard] at hZCcard16; omega

  -- Step 2: g² ∈ Z(G).  Since Z ≤ H has order 4 and |H| = 8,
  -- the quotient H/Z has order 2, so (gZ)² = Z, giving g² ∈ Z.
  have hg2_in_Z : g ^ 2 ∈ Z := by
    have hz_sub_equiv : Z.subgroupOf H ≃* Z := Subgroup.subgroupOfEquivOfLe hZ_le_H
    have hcard_Zsub : Nat.card (Z.subgroupOf H) = 4 := by
      rw [Nat.card_congr hz_sub_equiv.toEquiv, hZCcard]
    have hcard_quot : Nat.card (H ⧸ Z.subgroupOf H) = 2 := by
      have h_idx_mul := (Z.subgroupOf H).index_mul_card
      rw [Subgroup.index_eq_card, hcard_Zsub, hHcard] at h_idx_mul
      omega
    let g' : H := ⟨g, Subgroup.mem_zpowers g⟩
    -- The quotient H/Z has order 2, so (gZ)² = Z, i.e., g² ∈ Z
    have hg2_mem : g' ^ 2 ∈ Z.subgroupOf H := by
      have hcard_quot : Nat.card (H ⧸ Z.subgroupOf H) = 2 := by
        have hcard_Zsub : Nat.card (Z.subgroupOf H) = 4 := by
          have hequiv : Z.subgroupOf H ≃* Z := Subgroup.subgroupOfEquivOfLe hZ_le_H
          rw [Nat.card_congr hequiv.toEquiv, hZCcard]
        have h_idx_mul := (Z.subgroupOf H).index_mul_card
        rw [Subgroup.index_eq_card, hcard_Zsub, hHcard] at h_idx_mul
        omega
      -- In a group of order 2, every element squares to 1.
      -- Use the quotient group structure.
      have h_sq_one : ((QuotientGroup.mk g' : H ⧸ Z.subgroupOf H) ^ 2 : H ⧸ Z.subgroupOf H) = 1
      := by
        have := pow_card_eq_one' (x := (QuotientGroup.mk g' : H ⧸ Z.subgroupOf H))
        rw [hcard_quot] at this
        exact this
      have h_mk_sq : ((QuotientGroup.mk g' : H ⧸ Z.subgroupOf H) ^ 2 : H ⧸ Z.subgroupOf H) =
          QuotientGroup.mk (g' ^ 2 : H) := by simp
      rw [h_mk_sq] at h_sq_one
      exact (QuotientGroup.eq_one_iff (g' ^ 2 : H)).mp h_sq_one
    rw [Subgroup.mem_subgroupOf] at hg2_mem
    simpa [Z, g'] using hg2_mem

  -- Step 3: pick t ∉ H, prove t·g·t⁻¹ = g⁵
  have hH_ne_top : H ≠ ⊤ := by
    intro heq; rw [heq, Subgroup.card_top, hcard] at hHcard; omega
  obtain ⟨t, ht_not_H⟩ : ∃ t : G, t ∉ H := by
    by_contra! h_all
    apply hH_ne_top
    rw [Subgroup.eq_top_iff']; intro x
    exact h_all x

  -- Key relation: t·g²·t⁻¹ = g² (since g² ∈ Z(G))
  have h_conj_g2 : t * (g ^ 2) * t⁻¹ = g ^ 2 := by
    have hmem : g ^ 2 ∈ Z := hg2_in_Z
    rw [Subgroup.mem_center_iff] at hmem
    calc
      t * (g ^ 2) * t⁻¹ = (g ^ 2) * t * t⁻¹ := by rw [(hmem t).symm]
      _ = g ^ 2 * (t * t⁻¹) := by group
      _ = g ^ 2 * 1 := by simp
      _ = g ^ 2 := by simp

  -- Hence (t·g·t⁻¹)² = g²
  have h_sq_conj : (t * g * t⁻¹) ^ 2 = g ^ 2 := by
    calc
      (t * g * t⁻¹) ^ 2 = t * g * t⁻¹ * (t * g * t⁻¹) := by rw [sq]
      _ = t * g * (t⁻¹ * t) * g * t⁻¹ := by group
      _ = t * (g * g) * t⁻¹ := by group
      _ = t * (g ^ 2) * t⁻¹ := by rw [sq]
      _ = g ^ 2 := h_conj_g2

  -- t·g·t⁻¹ ∈ H (since H ⊴ G)
  have h_conj_mem : t * g * t⁻¹ ∈ H :=
    hHnorm.conj_mem g (Subgroup.mem_zpowers g) t

  -- Write t·g·t⁻¹ = g^k for some k : ℤ
  rcases Subgroup.mem_zpowers_iff.mp h_conj_mem with ⟨k, hk⟩
  -- hk : t * g * t⁻¹ = g ^ k

  -- From (t·g·t⁻¹)² = g² we get g^{2k} = g²
  have h_zpow_sq : (g : G) ^ (2 * (k : ℤ)) = (g : G) ^ (2 : ℤ) := by
    -- g^(2k) = (g^k)^(2:ℤ) = (g^k)*(g^k) = (t*g*t⁻¹)*(t*g*t⁻¹) = (t*g*t⁻¹)² = g²
    calc
      (g : G) ^ (2 * (k : ℤ)) = ((g : G) ^ (k : ℤ)) ^ (2 : ℤ) := by
        rw [← zpow_mul g (k : ℤ) (2 : ℤ), mul_comm (2 : ℤ) (k : ℤ)]
      _ = ((g : G) ^ (k : ℤ)) * ((g : G) ^ (k : ℤ)) := by rw [zpow_two]
      _ = (g ^ k) * (g ^ k) := rfl
      _ = (t * g * t⁻¹) * (g ^ k) := by rw [← hk]
      _ = (t * g * t⁻¹) * (t * g * t⁻¹) := by rw [← hk]
      _ = (t * g * t⁻¹) ^ 2 := by rw [sq]
      _ = g ^ 2 := h_sq_conj
      _ = (g : G) ^ (2 : ℤ) := (zpow_natCast g 2).symm

  have h_modEq : (2 : ℤ) * (k : ℤ) ≡ (2 : ℤ) [ZMOD (8 : ℤ)] := by
    have := (zpow_eq_zpow_iff_modEq (x := g) (m := 2 * (k : ℤ)) (n := (2 : ℤ))).mp h_zpow_sq
    rw [hg] at this; exact this

  -- In ZMod 8: 2*x = 2 has solutions x = 1, 5
  have h_sol : (Finset.filter (fun x : ZMod 8 => (2 : ZMod 8) * x = (2 : ZMod 8))
    (Finset.univ : Finset (ZMod 8))) = {(1 : ZMod 8), (5 : ZMod 8)} := by decide
  have h_eq_zmod8 : (2 : ZMod 8) * ((k : ℤ) : ZMod 8) = (2 : ZMod 8) := by
    have := (ZMod.intCast_eq_intCast_iff ((2 : ℤ) * (k : ℤ)) (2 : ℤ) (8 : ℕ)).mpr h_modEq
    simpa [map_mul, map_intCast] using this
  have h_mem : ((k : ℤ) : ZMod 8)
  ∈ Finset.filter (fun x : ZMod 8 => (2 : ZMod 8) * x = (2 : ZMod 8))
    Finset.univ := by
    apply Finset.mem_filter.mpr; exact ⟨Finset.mem_univ _, h_eq_zmod8⟩
  rw [h_sol] at h_mem
  rcases Finset.mem_insert.mp h_mem with (hk1 | hk5)
  · -- (k : ZMod 8) = 1 → g^k = g → t*g = g*t → G abelian, contradicting |Z(G)|=4
    sorry
  · -- (k : ZMod 8) = 5 → g^k = g⁵
    have hk_modEq_five : (k : ℤ) ≡ (5 : ℤ) [ZMOD (8 : ℤ)] :=
      (ZMod.intCast_eq_intCast_iff (k : ℤ) (5 : ℤ) 8).mp (Finset.mem_singleton.mp hk5)
    have h_gk_eq_g5 : (g : G) ^ (k : ℤ) = g ^ 5 := by
      have := (zpow_eq_zpow_iff_modEq (x := g) (m := (k : ℤ)) (n := (5 : ℤ))).mpr
        (by rw [hg]; exact hk_modEq_five)
      have h_eq : (g : G) ^ (5 : ℤ) = g ^ 5 := zpow_natCast g 5
      rw [h_eq] at this
      exact this
    -- hk : g ^ k = t * g * t⁻¹, so t * g * t⁻¹ = g ^ 5
    have h_conj_eq_g5 : t * g * t⁻¹ = g ^ 5 :=
      hk.symm.trans h_gk_eq_g5
    -- Step 4: find s ∈ G \ H with s² = 1 and s·g·s⁻¹ = g⁵
    -- (splitting of the extension 1 → C8 → G → C2 → 1)
    sorry

end Smallgroups.UsefulTheorems
