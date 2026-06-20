/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeOrderClassification
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Group.Conj

/-!
# The dihedral isomorphism for order `2p`

Core construction: a finite group `G` of order `2p` (`p` an odd prime) that contains an element `a`
of order `p` and an involution `b` inverting `a` (`b a b⁻¹ = a⁻¹`) is isomorphic to the dihedral
group `DihedralGroup p`.

The isomorphism is built as the injective homomorphism `r i ↦ aⁱ`, `sr i ↦ b aⁱ`; injectivity plus
the equality of cardinalities (`2p`) gives bijectivity.
-/

namespace Smallgroups.UsefulTheorems

open DihedralGroup

variable {G : Type*} [Group G]

/-- A finite group of order `2p` (`p` odd prime) with an element `a` of order `p` and an involution
`b` with `b a b⁻¹ = a⁻¹` is isomorphic to `DihedralGroup p`. -/
theorem nonempty_mulEquiv_dihedral {p : ℕ} (hp : p.Prime) (hodd : Odd p) [Finite G]
    (a b : G) (hap : orderOf a = p) (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (hcard : Nat.card G = 2 * p) :
    Nonempty (G ≃* DihedralGroup p) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype G := Fintype.ofFinite G
  have hap1 : a ^ p = 1 := by rw [← hap]; exact pow_orderOf_eq_one a
  -- `i ↦ a ^ i.val` turns addition in `ZMod p` into multiplication.
  have hc_add : ∀ i j : ZMod p, a ^ (i + j).val = a ^ i.val * a ^ j.val := by
    intro i j
    rw [← pow_add]
    apply pow_eq_pow_iff_modEq.mpr
    rw [hap, ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hc_sub : ∀ i j : ZMod p, a ^ (j - i).val = a ^ j.val * (a ^ i.val)⁻¹ := by
    intro i j
    have h := hc_add (j - i) i
    rw [sub_add_cancel] at h
    exact eq_mul_inv_iff_mul_eq.mpr h.symm
  -- the commutation relation `a * b = b * a⁻¹`, and its powers.
  have hab : a * b = b * a⁻¹ := by
    have h2 : b * a = a⁻¹ * b := by rw [← hba]; group
    have h : a * b * a = b := by
      calc a * b * a = a * (b * a) := by group
        _ = a * (a⁻¹ * b) := by rw [h2]
        _ = b := by group
    calc a * b = a * b * a * a⁻¹ := by group
      _ = b * a⁻¹ := by rw [h]
  have hak : ∀ k : ℕ, a ^ k * b = b * (a⁻¹) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, hab, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  -- powers of `a` commute (with each other and with inverses).
  have hcom : ∀ m n : ℕ, (a ^ m)⁻¹ * a ^ n = a ^ n * (a ^ m)⁻¹ := fun m n =>
    ((((Commute.refl a).pow_pow n m).inv_right).eq).symm
  -- helper rewrites for the reflection products.
  have hrsr : ∀ m n : ℕ, a ^ m * (b * a ^ n) = b * (a ^ n * (a ^ m)⁻¹) := by
    intro m n
    rw [← mul_assoc, hak, mul_assoc, inv_pow, hcom]
  have hsrsr : ∀ m n : ℕ, b * a ^ m * (b * a ^ n) = a ^ n * (a ^ m)⁻¹ := by
    intro m n
    rw [mul_assoc, hrsr, ← mul_assoc, ← pow_two, hb2, one_mul]
  -- the underlying map and its multiplicativity.
  let φ : DihedralGroup p → G := fun x => match x with
    | .r i => a ^ i.val
    | .sr i => b * a ^ i.val
  have hφmul : ∀ x y, φ (x * y) = φ x * φ y := by
    rintro (i | i) (j | j)
    · change a ^ (i + j).val = a ^ i.val * a ^ j.val
      exact hc_add i j
    · change b * a ^ (j - i).val = a ^ i.val * (b * a ^ j.val)
      rw [hc_sub, hrsr]
    · change b * a ^ (i + j).val = b * a ^ i.val * a ^ j.val
      rw [hc_add, mul_assoc]
    · change a ^ (j - i).val = b * a ^ i.val * (b * a ^ j.val)
      rw [hc_sub, hsrsr]
  let f : DihedralGroup p →* G := MonoidHom.mk' φ hφmul
  -- `f` is injective.
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro (i | i) hx
    · have hx' : a ^ i.val = 1 := hx
      have hdvd : orderOf a ∣ i.val := orderOf_dvd_of_pow_eq_one hx'
      rw [hap] at hdvd
      have hi0 : i = 0 := by
        rw [← ZMod.val_eq_zero]
        exact Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt i)
      rw [hi0]; exact one_def.symm
    · exfalso
      have hsr : b * a ^ i.val = 1 := hx
      have hbeq : b = (a ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left hsr
      have hbpow : b ^ p = 1 := by
        rw [hbeq, inv_pow, ← pow_mul, mul_comm i.val p, pow_mul, hap1, one_pow, inv_one]
      have hp2 : p = 2 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
          ((orderOf_eq_prime hb2 hb1) ▸ orderOf_dvd_of_pow_eq_one hbpow)).symm
      rw [hp2] at hodd
      exact (by decide : ¬ Odd 2) hodd
  -- injective + equal cardinality ⟹ bijective.
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by rw [DihedralGroup.card, ← Nat.card_eq_fintype_card, hcard]⟩
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

/-- **Exhaustiveness for order `2p`.** Every group of order `2p` (`p` an odd prime) is isomorphic
to the cyclic group `ℤ/2p` or to the dihedral group `DihedralGroup p`.

A subgroup `⟨a⟩` generated by an element of order `p` has index `2`, hence is normal, so conjugation
by an involution `b` sends `a` to some `aᵏ` with `k² ≡ 1 [MOD p]`; thus `k ≡ 1` (giving an abelian,
hence cyclic, group) or `k ≡ -1` (giving the dihedral relation `b a b⁻¹ = a⁻¹`). -/
theorem classification_card_two_mul_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hG : Nat.card G = 2 * p) :
    Nonempty (G ≃* CyclicRep (2 * p)) ∨ Nonempty (G ≃* DihedralGroup p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [hG]; exact Nat.mul_ne_zero two_ne_zero hp.pos.ne')
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p (G := G) ⟨2, by rw [hG]; ring⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 2 (G := G) ⟨p, by rw [hG]⟩
  have hb1 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; exact absurd hb (by norm_num)
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  -- `⟨a⟩` has index 2, hence is normal.
  have hAcard : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, ha]
  have hAindex : (Subgroup.zpowers a).index = 2 := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers a)
    rw [hAcard, hG] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos (h.trans (Nat.mul_comm 2 p))
  haveI hAnorm : (Subgroup.zpowers a).Normal := Subgroup.normal_of_index_eq_two hAindex
  -- `b a b⁻¹ = aᵏ`, and `k² ≡ 1 [MOD p]`.
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hAnorm.conj_mem a (Subgroup.mem_zpowers a) b)
  have hbb : b * b = 1 := by rw [← pow_two]; exact hb2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hconj2 : b * (b * a * b⁻¹) * b⁻¹ = a := by
    rw [hbinv]
    calc b * (b * a * b) * b = (b * b) * a * (b * b) := by group
      _ = a := by rw [hbb, one_mul, mul_one]
  have hkk : a ^ (k * k) = a := by rw [zpow_mul, hk, conj_zpow, hk, hconj2]
  have hk1 : a ^ (k * k - 1) = 1 := by
    rw [zpow_sub, hkk, zpow_one]; exact mul_inv_cancel a
  have hpd : (p : ℤ) ∣ (k - 1) * (k + 1) := by
    have h0 : (k * k - 1) ≡ 0 [ZMOD orderOf a] := zpow_eq_one_iff_modEq.mp hk1
    rw [ha, Int.modEq_zero_iff_dvd] at h0
    rwa [show (k - 1) * (k + 1) = k * k - 1 by ring]
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hpd with hd | hd
  · -- `k ≡ 1 [MOD p]` : `a` and `b` commute, so `G` is cyclic.
    left
    have hzz : a ^ (k - 1) = 1 := by
      rw [zpow_eq_one_iff_modEq, ha, Int.modEq_zero_iff_dvd]; exact hd
    have hak1 : a ^ k = a := by
      rw [zpow_sub, zpow_one] at hzz; exact mul_inv_eq_one.mp hzz
    have hba1 : b * a * b⁻¹ = a := by rw [← hk, hak1]
    have hcomm : Commute a b := by
      have hcm : b * a = a * b :=
        calc b * a = b * a * b⁻¹ * b := by group
          _ = a * b := by rw [hba1]
      exact hcm.symm
    have hcop : (orderOf a).Coprime (orderOf b) := by
      rw [ha, hb]; exact Nat.coprime_two_right.mpr hodd
    haveI : IsCyclic G := by
      have hord : orderOf (a * b) = 2 * p := by
        rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, ha, hb, Nat.mul_comm]
      exact isCyclic_of_orderOf_eq_card (a * b) (by rw [hord, hG])
    exact cyclicRep_classification (Nat.mul_ne_zero two_ne_zero hp.pos.ne') hG
  · -- `k ≡ -1 [MOD p]` : `b a b⁻¹ = a⁻¹`, the dihedral relation.
    right
    have hzz : a ^ (k + 1) = 1 := by
      rw [zpow_eq_one_iff_modEq, ha, Int.modEq_zero_iff_dvd]; exact hd
    have hkm1 : a ^ k = a⁻¹ := by
      rw [zpow_add, zpow_one] at hzz; exact mul_eq_one_iff_eq_inv.mp hzz
    have hba_rel : b * a * b⁻¹ = a⁻¹ := by rw [← hk, hkm1]
    exact nonempty_mulEquiv_dihedral hp hodd a b ha hb1 hb2 hba_rel hG

/-- The cyclic and dihedral groups of order `2p` (`p ≠ 1`) are not isomorphic: the dihedral one is
not cyclic. -/
theorem cyclicRep_not_mulEquiv_dihedral {p : ℕ} (hp1 : p ≠ 1) :
    ¬ Nonempty (CyclicRep (2 * p) ≃* DihedralGroup p) := by
  rintro ⟨e⟩
  exact DihedralGroup.not_isCyclic hp1 (e.isCyclic.mp inferInstance)

end Smallgroups.UsefulTheorems
