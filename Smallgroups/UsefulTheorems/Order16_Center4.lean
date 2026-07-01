/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Conj

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
    have hk_modEq_one : (k : ℤ) ≡ (1 : ℤ) [ZMOD (8 : ℤ)] :=
      (ZMod.intCast_eq_intCast_iff (k : ℤ) (1 : ℤ) 8).mp hk1
    have h_gk_eq_g : (g : G) ^ (k : ℤ) = g := by
      have := (zpow_eq_zpow_iff_modEq (x := g) (m := (k : ℤ)) (n := (1 : ℤ))).mpr
        (by rw [hg]; exact hk_modEq_one)
      simpa [zpow_one] using this
    have h_conj_eq_g : t * g * t⁻¹ = g :=
      hk.symm.trans h_gk_eq_g
    have h_comm_tg_eq : t * g = g * t := by
      calc
        t * g = (t * g * t⁻¹) * t := by group
        _ = g * t := by rw [h_conj_eq_g]
    have h_comm_tg : Commute t g := h_comm_tg_eq
    -- t commutes with all elements of H (H = ⟨g⟩)
    have h_comm_t_H (h : H) : Commute t (h : G) := by
      rcases Subgroup.mem_zpowers_iff.mp h.2 with ⟨n, hn⟩
      have hcomm : Commute t (g ^ n) := h_comm_tg.zpow_right n
      simpa [hn] using hcomm
    -- H is abelian (cyclic)
    have h_comm_H (h1 h2 : H) : Commute (h1 : G) (h2 : G) := by
      rcases Subgroup.mem_zpowers_iff.mp h1.2 with ⟨m, hm⟩
      rcases Subgroup.mem_zpowers_iff.mp h2.2 with ⟨n, hn⟩
      have hcomm : Commute (g ^ m) (g ^ n) := ((Commute.refl g).zpow_zpow m n)
      simpa [hm, hn] using hcomm
    -- Every x ∉ H can be written as h * t for some h ∈ H
    have h_coset (x : G) (hx : x ∉ H) : ∃ h : H, (h : G) * t = x := by
      have h_xt_H : x * t ∈ H := by
        have h_iff := Subgroup.mul_mem_iff_of_index_two (a := x) (b := t) hHindex
        apply h_iff.mpr
        simp [hx, ht_not_H]
      have h_sq_t_H : t ^ 2 ∈ H := Subgroup.sq_mem_of_index_two hHindex t
      have h_sq_t_inv_H : (t ^ 2)⁻¹ ∈ H := Subgroup.inv_mem _ h_sq_t_H
      have h_t2inv_t : (t ^ 2)⁻¹ * t = t⁻¹ := by group
      set h := (x * t) * (t ^ 2)⁻¹ with hh
      have h_mem_H : h ∈ H := Subgroup.mul_mem H h_xt_H h_sq_t_inv_H
      refine ⟨⟨h, h_mem_H⟩, ?_⟩
      calc
        (h : G) * t = ((x * t) * (t ^ 2)⁻¹) * t := rfl
        _ = (x * t) * ((t ^ 2)⁻¹ * t) := by group
        _ = (x * t) * t⁻¹ := by rw [h_t2inv_t]
        _ = x := by group
    -- Now prove G is abelian via case analysis
    have hab : ∀ a b : G, a * b = b * a := by
      intro a b
      by_cases haH : a ∈ H
      · by_cases hbH : b ∈ H
        · -- both in H
          exact (h_comm_H ⟨a, haH⟩ ⟨b, hbH⟩).eq
        · -- a ∈ H, b ∉ H → b = hb' * t
          rcases h_coset b hbH with ⟨hb', hb_eq⟩
          calc
            a * b = a * ((hb' : G) * t) := by rw [hb_eq]
            _ = (a * (hb' : G)) * t := by group
            _ = ((hb' : G) * a) * t := by rw [(h_comm_H ⟨a, haH⟩ hb').eq]
            _ = (hb' : G) * (a * t) := by group
            _ = (hb' : G) * (t * a) := by rw [(h_comm_t_H ⟨a, haH⟩).eq]
            _ = ((hb' : G) * t) * a := by group
            _ = b * a := by rw [← hb_eq]
      · by_cases hbH : b ∈ H
        · -- a ∉ H, b ∈ H → symmetric to above
          rcases h_coset a haH with ⟨ha', ha_eq⟩
          calc
            a * b = (ha' : G) * t * b := by rw [ha_eq]
            _ = (ha' : G) * (t * b) := by group
            _ = (ha' : G) * (b * t) := by rw [(h_comm_t_H ⟨b, hbH⟩).eq]
            _ = ((ha' : G) * b) * t := by group
            _ = (b * (ha' : G)) * t := by rw [(h_comm_H ha' ⟨b, hbH⟩).eq]
            _ = b * ((ha' : G) * t) := by group
            _ = b * a := by rw [← ha_eq]
        · -- both ∉ H
          rcases h_coset a haH with ⟨ha', ha_eq⟩
          rcases h_coset b hbH with ⟨hb', hb_eq⟩
          calc
            a * b = ((ha' : G) * t) * ((hb' : G) * t) := by rw [ha_eq, hb_eq]
            _ = (ha' : G) * (t * (hb' : G)) * t := by group
            _ = (ha' : G) * ((hb' : G) * t) * t := by rw [(h_comm_t_H hb').eq]
            _ = ((ha' : G) * (hb' : G)) * (t * t) := by group
            _ = ((hb' : G) * (ha' : G)) * (t * t) := by rw [(h_comm_H ha' hb').eq]
            _ = (hb' : G) * ((ha' : G) * t) * t := by group
            _ = (hb' : G) * (t * (ha' : G)) * t := by rw [(h_comm_t_H ha').eq]
            _ = ((hb' : G) * t) * ((ha' : G) * t) := by group
            _ = b * a := by rw [ha_eq, hb_eq]
    -- Contradiction: G abelian → |Z(G)| = 16, but we have |Z(G)| = 4
    have hZCcard16 : Nat.card (center G) = 16 := by
      rw [card_center_eq_card_of_comm G hab, hcard]
    rw [hZCcard] at hZCcard16
    omega
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
    -- g⁴ ∈ center G (since g² ∈ Z and g⁴ = (g²)²)
    have h_g4_central : g ^ 4 ∈ center G := by
      have h_sq_eq : g ^ 4 = (g ^ 2) * (g ^ 2) := by
        calc
          g ^ 4 = g ^ (2 + 2) := by norm_num
          _ = (g ^ 2) * (g ^ 2) := by rw [pow_add]
      rw [h_sq_eq]
      exact Subgroup.mul_mem (center G) hg2_in_Z hg2_in_Z
    have h_g4_central' (x : G) : (g ^ 4) * x = x * (g ^ 4) :=
      (Subgroup.mem_center_iff.mp h_g4_central x).symm
    have h_g4_inv : (g ^ 4)⁻¹ = g ^ 4 := by
      have h_sq : g ^ 4 * g ^ 4 = 1 := by
        calc
          g ^ 4 * g ^ 4 = g ^ (4 + 4) := by rw [pow_add]
          _ = g ^ 8 := by norm_num
          _ = 1 := hg8
      exact (eq_inv_of_mul_eq_one_left h_sq).symm
    have h_g_pow_add_4_1 : g ^ 4 * g = g * g ^ 4 := by
      calc
        g ^ 4 * g = g ^ (4 + 1) := by rw [← pow_succ]
        _ = g ^ 5 := by norm_num
        _ = g ^ (1 + 4) := by norm_num
        _ = g ^ 1 * g ^ 4 := by rw [pow_add]
        _ = g * g ^ 4 := by simp
    -- t⁻¹ * g * t = g⁵
    have h_conj_inv : t⁻¹ * g * t = g ^ 5 := by
      have h_g_eq : g = t⁻¹ * g ^ 5 * t := by
        calc
          g = t⁻¹ * (t * g * t⁻¹) * t := by group
          _ = t⁻¹ * (g ^ 5) * t := by rw [h_conj_eq_g5]
      have h_g5_eq : g ^ 5 = g * g ^ 4 := by
        calc
          g ^ 5 = g ^ (4 + 1) := by norm_num
          _ = g ^ 4 * g := by rw [pow_succ]
          _ = g * g ^ 4 := h_g_pow_add_4_1
      have h_g_eq2 : g = t⁻¹ * g * t * g ^ 4 := by
        calc
          g = t⁻¹ * (g ^ 5) * t := h_g_eq
          _ = t⁻¹ * (g * g ^ 4) * t := by rw [h_g5_eq]
          _ = (t⁻¹ * g) * (g ^ 4) * t := by group
          _ = t⁻¹ * g * (g ^ 4 * t) := by group
          _ = t⁻¹ * g * (t * g ^ 4) := by rw [h_g4_central' t]
          _ = t⁻¹ * g * t * g ^ 4 := by group
      calc
        t⁻¹ * g * t = (t⁻¹ * g * t * g ^ 4) * (g ^ 4)⁻¹ := by group
        _ = g * (g ^ 4)⁻¹ := by rw [← h_g_eq2]
        _ = g * g ^ 4 := by rw [h_g4_inv]
        _ = g ^ 5 := by
          calc
            g * g ^ 4 = g ^ 1 * g ^ 4 := by simp
            _ = g ^ (1 + 4) := by rw [pow_add]
            _ = g ^ 5 := by norm_num
    -- t² ∈ H, so t² = g^m for some m : ℤ
    have h_sq_t : t ^ 2 ∈ H := Subgroup.sq_mem_of_index_two hHindex t
    rcases Subgroup.mem_zpowers_iff.mp h_sq_t with ⟨m, hm⟩
    -- hm : g ^ (m : ℤ) = t ^ 2
    -- Prove m is even
    have hm_even : (2 : ℤ) ∣ (m : ℤ) := by
      have h_conj_sq : t * (t ^ 2) * t⁻¹ = t ^ 2 := by group
      rw [← hm] at h_conj_sq
      -- h_conj_sq : t * (g ^ (m : ℤ)) * t⁻¹ = g ^ (m : ℤ)
      have h_conj_zpow_lemma : t * g ^ (m : ℤ) * t⁻¹ = (t * g * t⁻¹) ^ (m : ℤ) :=
        (conj_zpow (a := t) (b := g) (i := m)).symm
      have h_conj_gm : t * (g ^ (m : ℤ)) * t⁻¹ = (t * g * t⁻¹) ^ (m : ℤ) := by
        simp only [h_conj_zpow_lemma]
      rw [h_conj_gm, h_conj_eq_g5] at h_conj_sq
      -- h_conj_sq : (g ^ 5) ^ (m : ℤ) = g ^ (m : ℤ)
      -- Convert (g^5) to (g^(5:ℤ)) for zpow_mul
      have h_temp_base : g ^ 5 = g ^ (5 : ℤ) := (zpow_natCast g 5).symm
      have h_convert : (g ^ 5) ^ (m : ℤ) = g ^ ((5 : ℤ) * (m : ℤ)) := by
        calc
          (g ^ 5) ^ (m : ℤ) = (g ^ (5 : ℤ)) ^ (m : ℤ) := by
            simpa using congrArg (· ^ (m : ℤ)) h_temp_base
          _ = g ^ ((5 : ℤ) * (m : ℤ)) := (zpow_mul g (5 : ℤ) (m : ℤ)).symm
      rw [h_convert] at h_conj_sq
      -- h_conj_sq : g ^ ((5 : ℤ) * (m : ℤ)) = g ^ (m : ℤ)
      have h_modEq := (zpow_eq_zpow_iff_modEq (x := g)
        (m := (5 : ℤ) * (m : ℤ)) (n := (m : ℤ))).mp h_conj_sq
      rw [hg] at h_modEq
      have h_four_modEq : (4 : ℤ) * (m : ℤ) ≡ (0 : ℤ) [ZMOD (8 : ℤ)] := by
        have h_refl : (m : ℤ) ≡ (m : ℤ) [ZMOD (8 : ℤ)] := by rfl
        have h_sub := h_modEq.sub h_refl
        have h_simp : (5 : ℤ) * (m : ℤ) - (m : ℤ) = (4 : ℤ) * (m : ℤ) := by ring
        simpa [h_simp, sub_self] using h_sub
      have h_dvd : (8 : ℤ) ∣ (4 : ℤ) * (m : ℤ) :=
        (Int.modEq_zero_iff_dvd (a := (4 : ℤ) * (m : ℤ)) (n := 8)).mp h_four_modEq
      omega
    rcases hm_even with ⟨k, hk⟩
    set s := t * (g ^ (k : ℤ)) with hs
    have h_conj_zpow_inv : ∀ (k : ℤ), t⁻¹ * g ^ k * t = (t⁻¹ * g * t) ^ k := by
      intro k
      simpa using (conj_zpow (a := t⁻¹) (b := g) (i := k)).symm
    have h_base5 : g ^ 5 = g ^ (5 : ℤ) := (zpow_natCast g 5).symm
    have h_gk_comm : g ^ (k : ℤ) * t = t * (g ^ ((5 : ℤ) * (k : ℤ))) := by
      calc
        g ^ (k : ℤ) * t = t * (t⁻¹ * g ^ (k : ℤ) * t) := by group
        _ = t * ((t⁻¹ * g * t) ^ (k : ℤ)) := by rw [h_conj_zpow_inv]
        _ = t * ((g ^ 5) ^ (k : ℤ)) := by rw [h_conj_inv]
        _ = t * ((g ^ (5 : ℤ)) ^ (k : ℤ)) := by
          simpa using congrArg (fun x => t * (x ^ (k : ℤ))) h_base5
        _ = t * (g ^ ((5 : ℤ) * (k : ℤ))) := by rw [zpow_mul g (5 : ℤ) (k : ℤ)]
    have hg_zpow8 : g ^ (8 : ℤ) = 1 :=
      (zpow_natCast g 8).trans hg8
    have hs_sq : s ^ 2 = 1 := by
      calc
        s ^ 2 = (t * (g ^ (k : ℤ))) * (t * (g ^ (k : ℤ))) := by rw [hs, sq]
        _ = t * g ^ (k : ℤ) * t * g ^ (k : ℤ) := by group
        _ = t * (g ^ (k : ℤ) * t) * g ^ (k : ℤ) := by group
        _ = t * (t * (g ^ ((5 : ℤ) * (k : ℤ)))) * g ^ (k : ℤ) := by rw [h_gk_comm]
        _ = (t ^ 2) * (g ^ ((5 : ℤ) * (k : ℤ))) * (g ^ (k : ℤ)) := by
          simp [sq, mul_assoc]
        _ = (g ^ (m : ℤ)) * (g ^ ((5 : ℤ) * (k : ℤ))) * (g ^ (k : ℤ)) := by rw [hm]
        _ = (g ^ ((2 : ℤ) * (k : ℤ))) * (g ^ ((5 : ℤ) * (k : ℤ))) * (g ^ (k : ℤ)) := by rw [hk]
         _ = (g ^ (((2 : ℤ) * (k : ℤ)) + ((5 : ℤ) * (k : ℤ)))) * (g ^ (k : ℤ)) := by
          rw [zpow_add g ((2 : ℤ) * (k : ℤ)) ((5 : ℤ) * (k : ℤ))]
        _ = (g ^ ((7 : ℤ) * (k : ℤ))) * (g ^ (k : ℤ)) := by ring
        _ = g ^ (((7 : ℤ) * (k : ℤ)) + (k : ℤ)) := by
          rw [zpow_add g ((7 : ℤ) * (k : ℤ)) (k : ℤ)]
        _ = g ^ ((8 : ℤ) * (k : ℤ)) := by ring
        _ = (g ^ (8 : ℤ)) ^ (k : ℤ) := by rw [zpow_mul g (8 : ℤ) (k : ℤ)]
        _ = 1 ^ (k : ℤ) := by rw [hg_zpow8]
        _ = 1 := by simp
    have hs_not_H : s ∉ H := by
      intro hsH
      have h_div : t ∈ H := by
        have : t = s * (g ^ (-(k : ℤ))) := by
          calc
            t = s * (g ^ (k : ℤ))⁻¹ := by
              dsimp [s]; group
            _ = s * (g ^ (-(k : ℤ))) := by rw [zpow_neg g (k : ℤ)]
        rw [this]
        have h_gk_inv_H : g ^ (-(k : ℤ)) ∈ H :=
        Subgroup.zpow_mem H (Subgroup.mem_zpowers g) (-(k : ℤ))
        exact Subgroup.mul_mem H hsH h_gk_inv_H
      exact ht_not_H h_div
    have hs_conj : s * g * s⁻¹ = g ^ 5 := by
      have h_comm_g_gnegk : Commute g (g ^ (-(k : ℤ))) :=
        (Commute.refl g).zpow_right (-(k : ℤ))
      have h_conj_gk_g : (g ^ (k : ℤ)) * g * (g ^ (k : ℤ))⁻¹ = g := by
        calc
          (g ^ (k : ℤ)) * g * (g ^ (k : ℤ))⁻¹ = (g ^ (k : ℤ)) * g * (g ^ (-(k : ℤ))) := by simp
          _ = (g ^ (k : ℤ)) * (g * g ^ (-(k : ℤ))) := by group
          _ = (g ^ (k : ℤ)) * (g ^ (-(k : ℤ)) * g) := by rw [h_comm_g_gnegk.eq]
          _ = ((g ^ (k : ℤ)) * g ^ (-(k : ℤ))) * g := by group
          _ = 1 * g := by simp
          _ = g := by simp
      calc
        s * g * s⁻¹ = (t * (g ^ (k : ℤ))) * g * (t * (g ^ (k : ℤ)))⁻¹ := by rw [hs]
        _ = t * (g ^ (k : ℤ)) * g * ((g ^ (k : ℤ))⁻¹ * t⁻¹) := by group
        _ = t * ((g ^ (k : ℤ)) * g * (g ^ (k : ℤ))⁻¹) * t⁻¹ := by group
        _ = t * g * t⁻¹ := by rw [h_conj_gk_g]
        _ = g ^ 5 := h_conj_eq_g5

    -- Step 5: Build isomorphism G ≃* order16_N1
    let K : Subgroup G := Subgroup.zpowers s
    have h_s_ne_one : s ≠ 1 := by
      intro h_eq
      apply hs_not_H
      rw [h_eq]
      exact Subgroup.one_mem H
    have h_order_s : orderOf s = 2 := by
      have h_dvd : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one (x := s) (n := 2) hs_sq
      have h_ne_one : orderOf s ≠ 1 := by
        intro h
        apply h_s_ne_one
        exact orderOf_eq_one_iff.mp h
      have h_pos : 0 < orderOf s := orderOf_pos s
      have h_le : orderOf s ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd
      interval_cases orderOf s
      · exact absurd rfl h_ne_one
      · rfl
    have hKcard : Nat.card K = 2 := by
      rw [Nat.card_zpowers, h_order_s]
    have h_card_mul : Nat.card H * Nat.card K = Nat.card G := by
      calc
        Nat.card H * Nat.card K = 8 * 2 := by rw [hHcard, hKcard]
        _ = 16 := by norm_num
        _ = Nat.card G := by rw [hcard]
    -- H and K are disjoint
    have h_s_zpow2 : s ^ (2 : ℤ) = 1 :=
      (zpow_natCast s 2).trans hs_sq
    have h_disjoint : Disjoint H K := by
      refine (Subgroup.disjoint_def (H₁ := H) (H₂ := K)).mpr ?_
      intro x hxH hxK
      rcases Subgroup.mem_zpowers_iff.mp hxK with ⟨b, hb⟩
      rcases Int.even_or_odd b with (⟨k, hk⟩ | ⟨k, hk⟩)
      · -- b = 2*k → s^b = 1 → x = 1
        have hs_b_one : s ^ (b : ℤ) = 1 := by
          rw [hk, ← two_mul (k : ℤ), zpow_mul, h_s_zpow2]
          simp
        rw [← hb, hs_b_one]
      · -- b = 2*k + 1 → s^b = s → x = s, contradicting s ∉ H
        have hs_b_s : s ^ (b : ℤ) = s := by
          rw [hk]
          rw [zpow_add_one, zpow_mul, h_s_zpow2]
          simp
        have hs_eq_x : s = x := by
          calc
            s = s ^ (b : ℤ) := hs_b_s.symm
            _ = x := hb
        have hsH : s ∈ H := hs_eq_x.symm ▸ hxH
        exact absurd hsH hs_not_H
    -- H and K are complementary
    have h_complement : H.IsComplement' K :=
      isComplement'_of_card_mul_and_disjoint h_card_mul h_disjoint
    -- Isomorphism G ≅ H ⋊ K via internal semidirect product
    have h_iso_sd : G ≃* (H ⋊[(H.normalizerMonoidHom).comp
      (Subgroup.inclusion (H.normalizer_eq_top ▸ le_top : K ≤ Subgroup.normalizer H))] K) :=
      (SemidirectProduct.mulEquivSubgroup h_complement).symm
    -- Now build an isomorphism from H ⋊ K to order16_N1
    -- H = ⟨g⟩ ≅ Z/8Z, K = ⟨s⟩ ≅ Z/2Z, and the action sgs⁻¹ = g⁵ matches x ↦ 5x
    -- order16_N1 = (Z/8Z) ⋊ (Z/2Z) via x ↦ 5x
    -- By the classification of semidirect products C8 ⋊ C2 with action x ↦ 5x,
    -- any two such semidirect products are isomorphic.
    -- This is a standard fact: there is only one non-abelian C8 ⋊ C2 with this action.
    sorry

end Smallgroups.UsefulTheorems
