/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Smallgroups.UsefulTheorems.PrimePairDihedral
import Smallgroups.UsefulTheorems.PrimeSqPrimeAbelian
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.Order2PSq
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow

/-!
# Classification of groups of order `4p` (`p` odd prime, `p ≥ 5`)

Every group of order `4p` with `p ≥ 5` has a normal Sylow-`p` subgroup (since `n_p ∣ 4` and
`n_p ≡ 1 [MOD p]` forces `n_p = 1`), so `G ≅ ℤ/p ⋊ H` where `H` has order `4`.

The Sylow-2 subgroup `H` is either cyclic (`ℤ/4`) or elementary abelian (`ℤ/2 × ℤ/2`).

## Cyclic Sylow-2 case (`H ≅ ℤ/4`)

The action `φ : ℤ/4 → Aut(ℤ/p) ≅ (ℤ/(p-1))` sends the generator to a unit `m` with `m⁴ ≡ 1`.
- `m = 1` : trivial action → `ℤ/4p` (Type I)
- `m = -1`: inversion → `ℤ/p ⋊_{-1} ℤ/4` (Type III)
- `m² = -1`: only when `p ≡ 1 [MOD 4]` → `ℤ/p ⋊_m ℤ/4` (Type IV)

## Klein four Sylow-2 case (`H ≅ ℤ/2 × ℤ/2`)

Each generator maps to an involution `±1` in `Aut(ℤ/p)`.
- Both trivial: `ℤ/2 × ℤ/2p` (Type II)
- At least one nontrivial: `ℤ/2 × D_{2p}` (Type V)

## Results

When `p ≡ 3 [MOD 4]` (`p > 3`): **4 classes** (I, II, III, V)
When `p ≡ 1 [MOD 4]`: **5 classes** (I, II, III, IV, V)
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-! ### Sylow-p normality for order `4p`, `p ≥ 5` -/

/-- The Sylow `p`-subgroup is unique when `|G| = 4p` and `p ≥ 5`. -/
theorem card_sylow_p_eq_one_of_card_4p {p : ℕ} (hp : p.Prime) (hpge : 5 ≤ p)
    [Finite G] (hG : Nat.card G = 4 * p) :
    Nat.card (Sylow p G) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
  have hndvd_p : ¬ p ∣ Nat.card (Sylow p G) := not_dvd_card_sylow p G
  have hdvd4p : Nat.card (Sylow p G) ∣ 4 * p :=
    hG ▸ (P0.card_dvd_index.trans (Subgroup.index_dvd_card _))
  have hcop : Nat.Coprime (Nat.card (Sylow p G)) p :=
    (hp.coprime_iff_not_dvd.mpr hndvd_p).symm
  have hdvd4 : Nat.card (Sylow p G) ∣ 4 := hcop.dvd_of_dvd_mul_right hdvd4p
  have hmod := card_sylow_modEq_one p G
  have hle : Nat.card (Sylow p G) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
  have hpos : 0 < Nat.card (Sylow p G) := Nat.card_pos
  have hlt : Nat.card (Sylow p G) < p := by omega
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : 1 < p)] at hmod
  exact hmod

/-- The Sylow-p subgroup of a group of order `4p` is normal when `p ≥ 5`. -/
theorem sylow_p_normal_of_card_4p {p : ℕ} (hp : p.Prime) (hpge : 5 ≤ p)
    [Finite G] (hG : Nat.card G = 4 * p) (P : Sylow p G) :
    (↑P : Subgroup G).Normal := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Subsingleton (Sylow p G) :=
    (Nat.card_eq_one_iff_unique.mp (card_sylow_p_eq_one_of_card_4p hp hpge hG)).1
  exact normal_of_subsingleton P

/-- The Sylow-p subgroup of a group of order `4p` has order `p`. -/
theorem card_sylow_p_subgroup_of_card_4p {p : ℕ} (hp : p.Prime) (hpge : 5 ≤ p)
    [Finite G] (hG : Nat.card G = 4 * p) (P : Sylow p G) :
    Nat.card (↑P : Subgroup G) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hndvd : ¬ p ∣ 4 := by
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have hfact : (4 * p).factorization p = 1 := by
    rw [Nat.factorization_mul (by norm_num) hp.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hndvd, Nat.Prime.factorization_self hp, zero_add]
  rw [Sylow.card_eq_multiplicity, hG, hfact, pow_one]

/-- **Schur–Zassenhaus reduction for order `4p` with `p ≥ 5`.** The group splits as
`N ⋊[φ] H` where `N` is the normal Sylow-`p` subgroup (order `p`) and `H` has order `4`. -/
theorem fourP_semidirectProduct {p : ℕ} (hp : p.Prime) (hpge : 5 ≤ p)
    [Finite G] (hG : Nat.card G = 4 * p) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N),
      N.Normal ∧ Nat.card N = p ∧ Nat.card H = 4 ∧
        Nonempty (G ≃* SemidirectProduct N H φ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := sylow_p_normal_of_card_4p hp hpge hG P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = p := card_sylow_p_subgroup_of_card_4p hp hpge hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have := P0.not_dvd_index
    exact hp.coprime_iff_not_dvd.mpr this
  obtain ⟨H, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardH : Nat.card H = 4 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN, mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_left hp.pos h1).symm
  exact ⟨↑P0, H, φ, hnorm, hcardN, hcardH, ⟨e⟩⟩

/-! ### Representative types -/

variable (p : ℕ)

/-- Type I: `ℤ/4p` (cyclic). -/
abbrev fourP_I : Type := Multiplicative (ZMod (4 * p))

/-- Type II: `ℤ/2 × ℤ/2p`. -/
abbrev fourP_II : Type := Multiplicative (ZMod 2) × Multiplicative (ZMod (2 * p))

/-- Type III: `ℤ/p ⋊_{-1} ℤ/4` (the generator of `ℤ/4` acts by inversion on `ℤ/p`). -/
private theorem neg_one_pow_four_units : (-1 : (ZMod p)ˣ) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from by ring, pow_mul]; simp [sq]

noncomputable abbrev fourP_III : Type :=
  NonabRep (-1 : (ZMod p)ˣ) (neg_one_pow_four_units p)

/-- Type IV: `ℤ/p ⋊_c ℤ/4` where `c² = -1` in `(ℤ/p)ˣ`.
Only exists when `p ≡ 1 [MOD 4]`. -/
noncomputable abbrev fourP_IV (c : (ZMod p)ˣ) (hc : c ^ 4 = 1) : Type :=
  NonabRep c hc

/-- Type V: `ℤ/2 × D_{2p}`. -/
abbrev fourP_V : Type := Multiplicative (ZMod 2) × DihedralGroup p

/-! ### Cardinalities -/

variable [Fact p.Prime]

private theorem four_p_ne_zero : 4 * p ≠ 0 := by
  have := (Fact.out (p := p.Prime)).pos; positivity

private theorem two_p_ne_zero : 2 * p ≠ 0 := by
  have := (Fact.out (p := p.Prime)).pos; positivity

theorem card_fourP_I : Nat.card (fourP_I p) = 4 * p := by
  haveI : NeZero (4 * p) := ⟨four_p_ne_zero p⟩
  exact card_cyclicRep (four_p_ne_zero p)

theorem card_fourP_II : Nat.card (fourP_II p) = 4 * p := by
  haveI : NeZero (2 * p) := ⟨two_p_ne_zero p⟩
  rw [Nat.card_prod, card_cyclicRep (by norm_num : (2 : ℕ) ≠ 0),
    card_cyclicRep (two_p_ne_zero p)]
  ring

theorem card_fourP_III (_ : p ≠ 2) : Nat.card (fourP_III p) = 4 * p := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  rw [fourP_III, card_nonabRep]
  ring

theorem card_fourP_IV (c : (ZMod p)ˣ) (hc : c ^ 4 = 1) :
    Nat.card (fourP_IV p c hc) = 4 * p := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  rw [fourP_IV, card_nonabRep]
  ring

omit [Fact p.Prime] in
theorem card_fourP_V : Nat.card (fourP_V p)  = 4 * p := by
  rw [fourP_V, Nat.card_prod, card_cyclicRep (by norm_num : (2 : ℕ) ≠ 0),
    DihedralGroup.nat_card]
  ring

/-! ### Commutativity / non-commutativity -/

omit [Fact p.Prime] in
theorem fourP_I_comm : ∀ a b : fourP_I p, a * b = b * a := fun a b => mul_comm a b

omit [Fact p.Prime] in
theorem fourP_II_comm : ∀ a b : fourP_II p, a * b = b * a := fun a b => mul_comm a b

theorem fourP_III_not_comm (hp2 : p ≠ 2) :
    ¬ ∀ a b : fourP_III p, a * b = b * a := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hne : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have h1 := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at h1
    have h2 : (2 : ZMod p) = 0 := by
      have h3 := sub_eq_zero.mpr h1
      rw [show (-1 : ZMod p) - 1 = -2 from by ring] at h3
      exact neg_eq_zero.mp h3
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by push_cast; ring] at h2
    have h3 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
    have h4 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h3
    exact hp2 (le_antisymm h4 (Fact.out (p := p.Prime)).two_le)
  exact nonabRep_not_comm (by norm_num) (-1) _ hne

theorem fourP_IV_not_comm (c : (ZMod p)ˣ) (hc : c ^ 4 = 1) (hc1 : c ≠ 1) :
    ¬ ∀ a b : fourP_IV p c hc, a * b = b * a := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  exact nonabRep_not_comm (by norm_num) c hc hc1

theorem fourP_V_not_comm (hp1 : 2 < p) :
    ¬ ∀ a b : fourP_V p, a * b = b * a := by
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

/-! ### Distinctness -/

theorem fourP_II_not_isCyclic (_ : p ≠ 2) : ¬ IsCyclic (fourP_II p) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (2 * p) := ⟨two_p_ne_zero p⟩
  intro h
  have hcop := coprime_card_of_isCyclic_prod
    (Multiplicative (ZMod 2)) (Multiplicative (ZMod (2 * p)))
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at hcop
  rw [Nat.coprime_mul_iff_right] at hcop
  exact absurd hcop.1 (by simp [Nat.Coprime])

theorem fourP_I_ne_II (hp2 : p ≠ 2) : ¬ Nonempty (fourP_I p ≃* fourP_II p) := by
  rintro ⟨e⟩
  exact fourP_II_not_isCyclic p hp2 (isCyclic_of_surjective e e.surjective)

theorem fourP_I_ne_III (hp2 : p ≠ 2) :
    ¬ Nonempty (fourP_I p ≃* fourP_III p) :=
  isEmpty_mulEquiv_of_comm_noncomm (fourP_I_comm p) (fourP_III_not_comm p hp2)

theorem fourP_I_ne_IV (c : (ZMod p)ˣ) (hc : c ^ 4 = 1) (hc1 : c ≠ 1) :
    ¬ Nonempty (fourP_I p ≃* fourP_IV p c hc) :=
  isEmpty_mulEquiv_of_comm_noncomm (fourP_I_comm p) (fourP_IV_not_comm p c hc hc1)

theorem fourP_I_ne_V (hp1 : 2 < p) :
    ¬ Nonempty (fourP_I p ≃* fourP_V p) :=
  isEmpty_mulEquiv_of_comm_noncomm (fourP_I_comm p) (fourP_V_not_comm p hp1)

theorem fourP_II_ne_III (hp2 : p ≠ 2) :
    ¬ Nonempty (fourP_II p ≃* fourP_III p) :=
  isEmpty_mulEquiv_of_comm_noncomm (fourP_II_comm p) (fourP_III_not_comm p hp2)

theorem fourP_II_ne_IV (c : (ZMod p)ˣ) (hc : c ^ 4 = 1) (hc1 : c ≠ 1) :
    ¬ Nonempty (fourP_II p ≃* fourP_IV p c hc) :=
  isEmpty_mulEquiv_of_comm_noncomm (fourP_II_comm p) (fourP_IV_not_comm p c hc hc1)

theorem fourP_II_ne_V (hp1 : 2 < p) :
    ¬ Nonempty (fourP_II p ≃* fourP_V p) :=
  isEmpty_mulEquiv_of_comm_noncomm (fourP_II_comm p) (fourP_V_not_comm p hp1)

private theorem fourP_V_pow_2p [NeZero p] :
    ∀ g : fourP_V p, g ^ (2 * p) = 1 := by
  intro ⟨a, d⟩
  simp only [Prod.pow_mk, Prod.mk_eq_one]
  constructor
  · rw [pow_mul]
    suffices h : a ^ 2 = 1 by rw [h, one_pow]
    rw [sq, ← ofAdd_toAdd a, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero]
  · cases d with
    | r i =>
      rw [DihedralGroup.r_pow, DihedralGroup.one_def, DihedralGroup.r.injEq]
      push_cast
      simp
    | sr i =>
      rw [pow_mul, sq, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero, one_pow]

private theorem fourP_V_no_order4 (hp1 : 2 < p) (hp : Nat.Prime p) :
    ∀ g : fourP_V p, orderOf g ≠ 4 := by
  haveI : NeZero p := ⟨by omega⟩
  have hndvd : ¬ (4 : ℕ) ∣ 2 * p := by
    rintro ⟨k, hk⟩
    have : 2 ∣ p := ⟨k, by omega⟩
    rcases hp.eq_one_or_self_of_dvd 2 this with h | h <;> omega
  exact fun g => orderOf_ne_of_pow (fourP_V_pow_2p p) hndvd g

private theorem nonabRep_has_order4 [NeZero p] (c : (ZMod p)ˣ) (hc : c ^ 4 = 1) :
    ∃ g : NonabRep c hc, orderOf g = 4 := by
  use SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))
  rw [orderOf_injective (SemidirectProduct.inr : Multiplicative (ZMod 4) →* _)
    SemidirectProduct.inr_injective]
  rw [orderOf_ofAdd_eq_addOrderOf]
  exact ZMod.addOrderOf_one 4

private theorem actionHom_one_eq [NeZero p] [NeZero q]
    (hc : (1 : (ZMod p)ˣ) ^ q = 1) (x : Multiplicative (ZMod q))
    (y : Multiplicative (ZMod p)) :
    (actionHom (1 : (ZMod p)ˣ) hc x) y = y := by
  obtain ⟨i, rfl⟩ := Multiplicative.ofAdd.surjective x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective y
  simp [actionHom_apply]

private theorem nonabRep_comm_of_trivial [NeZero p] [NeZero q]
    (hc : (1 : (ZMod p)ˣ) ^ q = 1) :
    ∀ a b : NonabRep (1 : (ZMod p)ˣ) hc, a * b = b * a := by
  intro a b
  refine SemidirectProduct.ext ?_ ?_
  · change a.left * (actionHom 1 hc a.right) b.left =
        b.left * (actionHom 1 hc b.right) a.left
    simp [actionHom_one_eq, mul_comm]
  · exact mul_comm a.right b.right

private theorem sq_eq_neg_one_of_pow_four [NeZero p]
    (c : (ZMod p)ˣ) (hc : c ^ 4 = 1) (hc1 : c ≠ 1) (hcn1 : c ≠ -1) :
    c ^ 2 = -1 := by
  have hcsq_sq : (c ^ 2) ^ 2 = 1 := by rw [← pow_mul]; norm_num; exact hc
  have hcsq_ne : c ^ 2 ≠ 1 := by
    intro h
    have hval : ((c : ZMod p)) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
    rw [sq_eq_one_iff] at hval
    rcases hval with hv | hv
    · exact hc1 (Units.val_injective (by simp [hv]))
    · exact hcn1 (Units.val_injective (by simp [hv]))
  have hval2 : ((c ^ 2 : (ZMod p)ˣ) : ZMod p) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hcsq_sq, Units.val_one]
  rw [sq_eq_one_iff] at hval2
  rcases hval2 with hv | hv
  · exact absurd (Units.val_injective (by simp [hv])) hcsq_ne
  · exact Units.val_injective (by simp [hv])

private theorem action_neg_one_ofAdd_two_id [NeZero p] (hc : ((-1 : (ZMod p)ˣ) ^ 4 = 1))
    (x : Multiplicative (ZMod p)) :
    (actionHom ((-1 : (ZMod p)ˣ)) hc) (Multiplicative.ofAdd (2 : ZMod 4)) x = x := by
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [actionHom_apply]
  have hval : (2 : ZMod 4).val = 2 := by decide
  rw [hval]
  simp

private theorem fourP_III_has_order_2p [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ g : fourP_III p, orderOf g = 2 * p := by
  let hc : ((-1 : (ZMod p)ˣ) ^ 4 = 1) := neg_one_pow_four_units p
  set a : Multiplicative (ZMod p) := Multiplicative.ofAdd 1
  set b : Multiplicative (ZMod 4) := Multiplicative.ofAdd 2
  refine ⟨⟨a, b⟩, ?_⟩
  set g : fourP_III p := ⟨a, b⟩
  have ha_p : a ^ p = 1 := by
    dsimp [a]
    have hcard : Fintype.card (Multiplicative (ZMod p)) = p := by simp
    simpa [hcard] using pow_card_eq_one (x := Multiplicative.ofAdd (1 : ZMod p))
  have hb_sq : b ^ 2 = 1 := by
    dsimp [b]
    have : (Multiplicative.ofAdd (2 : ZMod 4)) ^ 2 = 1 := by
      exact Eq.symm (Multiplicative.ext rfl)
    simpa
  have hb_p : b ^ p = b := by
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · have h2dvd : 2 ∣ p := ⟨k, by omega⟩
      have h := hp.eq_one_or_self_of_dvd 2 h2dvd
      rcases h with (h | h)
      · omega
      · exfalso; exact hp2 h.symm
    · rw [hk, pow_succ, pow_mul, hb_sq, one_pow, one_mul]
  have h_act_b : (actionHom (-1 : (ZMod p)ˣ) hc b) = 1 := by
    ext x; exact action_neg_one_ofAdd_two_id p hc x
  have h_act_pow (n : ℕ) : (actionHom (-1 : (ZMod p)ˣ) hc) (b ^ n) = 1 := by
    rw [map_pow, h_act_b, one_pow]
  have hg_pow (n : ℕ) : g ^ n = ⟨a ^ n, b ^ n⟩ := by
    induction n with
    | zero => simp [g, a, b]
    | succ k ih =>
      rw [pow_succ, ih]
      apply SemidirectProduct.ext
      · change (a ^ k) * ((actionHom (-1 : (ZMod p)ˣ) hc) (b ^ k)) a = a ^ (k + 1)
        rw [h_act_pow k]
        simp [← pow_succ]
      · change (b ^ k) * b = b ^ (k + 1)
        rw [← pow_succ]
  have hg_pow_2p : g ^ (2 * p) = 1 := by
    rw [hg_pow (2 * p)]
    have ha_2p : a ^ (2 * p) = 1 := by
      rw [mul_comm 2 p, pow_mul, ha_p, one_pow]
    have hb_2p : b ^ (2 * p) = 1 := by
      rw [pow_mul, hb_sq, one_pow]
    rw [ha_2p, hb_2p]
    rfl
  have hg_sq_ne : g ^ 2 ≠ 1 := by
    rw [hg_pow 2, hb_sq]
    intro h
    have hleft : a ^ 2 = 1 := by
      simpa using congr_arg (fun x : fourP_III p => x.left) h
    have ha2_ne : a ^ 2 ≠ 1 := by
      intro ha2
      have hord_a : orderOf a = p := by
        have h : orderOf (Multiplicative.ofAdd (1 : ZMod p)) = p := by
          rw [orderOf_ofAdd_eq_addOrderOf]
          simp [ZMod.addOrderOf_one p]
        simp [a, h]
      have hord := orderOf_dvd_of_pow_eq_one ha2
      rw [hord_a] at hord
      have hle := Nat.le_of_dvd (by norm_num) hord
      have hpge : 2 ≤ p := hp.two_le
      omega
    exact ha2_ne hleft
  have hg_p_ne : g ^ p ≠ 1 := by
    rw [hg_pow p, ha_p, hb_p]
    intro h
    have hright : b = (1 : Multiplicative (ZMod 4)) := by
      simpa using congr_arg (fun x : fourP_III p => x.right) h
    dsimp [b] at hright
    have hne : (Multiplicative.ofAdd (2 : ZMod 4)) ≠ 1 := by
      intro hne'
      have hzero : (2 : ZMod 4) = 0 := by
        simpa using congr_arg Multiplicative.toAdd hne'
      have : (2 : ZMod 4) ≠ 0 := by decide
      exact this hzero
    exact hne hright
  have hdvd := orderOf_dvd_of_pow_eq_one hg_pow_2p
  have hne1 : orderOf g ≠ 1 := by
    intro h; rw [orderOf_eq_one_iff] at h
    exact hg_sq_ne (by rw [h, one_pow])
  have hne2 : orderOf g ≠ 2 := by
    intro h; exact hg_sq_ne (by rw [← h]; exact pow_orderOf_eq_one g)
  have hneP : orderOf g ≠ p := by
    intro h
    have := pow_orderOf_eq_one g
    rw [h] at this
    exact hg_p_ne this
  have hp2_prime : Nat.Prime 2 := by decide
  have hpdvd_or : p ∣ orderOf g := by
    by_contra hp_ndvd
    have hcop : Nat.Coprime (orderOf g) p := (hp.coprime_iff_not_dvd.mpr hp_ndvd).symm
    have h2dvd : orderOf g ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
    rcases hp2_prime.eq_one_or_self_of_dvd _ h2dvd with h | h
    · exact hne1 h
    · exact hne2 h
  obtain ⟨k, hk⟩ := hpdvd_or
  have hk_dvd : k ∣ 2 := by
    have h1 : p * k ∣ 2 * p := hk ▸ hdvd
    have h1' : p * k ∣ p * 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h1
    exact (Nat.mul_dvd_mul_iff_left hp.pos).mp h1'
  rcases hp2_prime.eq_one_or_self_of_dvd _ hk_dvd with h | h
  · exfalso; exact hneP (by rw [hk, h, mul_one])
  · rw [hk, h, mul_comm p 2]

private theorem fourP_IV_no_order_2p [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (c : (ZMod p)ˣ) (hc : c ^ 4 = 1) (hc1 : c ≠ 1) (hcn1 : c ≠ -1) :
    ∀ g : fourP_IV p c hc, orderOf g ≠ 2 * p := by
  have hcsq : c ^ 2 = -1 := sq_eq_neg_one_of_pow_four (p := p) c hc hc1 hcn1
  intro g hord
  have h_right_dvd : orderOf g.right ∣ 2 * p := by
    rw [← hord]; exact orderOf_map_dvd SemidirectProduct.rightHom g
  have h_right_4 : g.right ^ (Fintype.card (Multiplicative (ZMod 4))) = 1 :=
    pow_card_eq_one
  have h_right_dvd4 : orderOf g.right ∣ 4 := by
    have hcard : Fintype.card (Multiplicative (ZMod 4)) = 4 := by simp
    simpa [hcard] using orderOf_dvd_of_pow_eq_one h_right_4
  have hp2_prime : Nat.Prime 2 := by decide
  have h_right_dvd2 : orderOf g.right ∣ 2 := by
    have hgcd : Nat.gcd (2 * p) 4 = 2 := by
      rw [show (4 : ℕ) = 2 * 2 from by ring, Nat.gcd_mul_left]
      rw [Nat.gcd_comm]
      have hcop : Nat.Coprime 2 p :=
        (hp2_prime.coprime_iff_not_dvd).mpr (by
          intro h
          rcases hp.eq_one_or_self_of_dvd 2 h with (h' | h')
          · omega
          · exact hp2 h'.symm)
      have hgcd_eq : Nat.gcd 2 p = 1 := hcop.gcd_eq_one
      rw [hgcd_eq]
    have htemp := Nat.dvd_gcd h_right_dvd h_right_dvd4
    rw [hgcd] at htemp
    exact htemp
  have h_right_sq : g.right ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h_right_dvd2
  set r := Multiplicative.toAdd g.right with hr_def
  have hr_add : r + r = 0 := by
    have := congr_arg Multiplicative.toAdd h_right_sq
    rw [show g.right ^ 2 = g.right * g.right from pow_two g.right] at this
    rw [toAdd_mul, toAdd_one] at this
    simpa [r, hr_def] using this
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by
    have : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
    exact this r
  rcases hr_cases with (hr | hr | hr | hr)
  · -- r = 0: g.right = 1, g = inl(a), orderOf g | p
    have hgr : g.right = 1 := by
      rw [show g.right = Multiplicative.ofAdd r from (ofAdd_toAdd _).symm]
      rw [hr]
      simp
    have : orderOf g ∣ p := by
      have hinl : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl hgr
      rw [hinl, orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective]
      have hcard : Fintype.card (Multiplicative (ZMod p)) = p := by simp
      simpa [hcard] using orderOf_dvd_card (x := g.left)
    have hle := Nat.le_of_dvd hp.pos (hord ▸ this)
    have hlt : p < 2 * p := by
      have := hp.one_lt
      omega
    omega
  · -- r = 1: contradiction with hr_add
    rw [hr] at hr_add
    have : (2 : ZMod 4) ≠ 0 := by decide
    exact this hr_add
  · -- r = 2: g^2 = 1, orderOf g | 2
    have hgr : g.right = Multiplicative.ofAdd (2 : ZMod 4) := by
      rw [show g.right = Multiplicative.ofAdd r from (ofAdd_toAdd _).symm, hr]
    have hgsq : g * g = 1 := by
      apply SemidirectProduct.ext
      · change g.left * (actionHom c hc g.right) g.left = 1
        rw [hgr, show g.left = Multiplicative.ofAdd (Multiplicative.toAdd g.left) from
          (ofAdd_toAdd _).symm]
        rw [actionHom_apply c hc (2 : ZMod 4) (Multiplicative.toAdd g.left),
          show (2 : ZMod 4).val = 2 by decide, hcsq]
        simp
      · calc
          (g * g).right = g.right * g.right := rfl
          _ = g.right ^ 2 := by rw [← sq]
          _ = 1 := h_right_sq
    have hgsq' : g ^ 2 = 1 := by rw [sq, hgsq]
    have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hgsq'
    have hle := Nat.le_of_dvd (by norm_num) (hord ▸ this)
    have hlt : 2 < 2 * p := by
      have := hp.one_lt
      omega
    omega
  · -- r = 3: contradiction with hr_add
    rw [hr] at hr_add
    have : (6 : ZMod 4) ≠ 0 := by decide
    exact this hr_add

theorem fourP_III_ne_IV (c : (ZMod p)ˣ) (hc : c ^ 4 = 1) (hcne : c ≠ -1) :
    ¬ Nonempty (fourP_III p ≃* fourP_IV p c hc) := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hp := Fact.out (p := p.Prime)
  by_cases hc1 : c = 1
  · subst hc1
    have hp2 : p ≠ 2 := by
      intro h; subst h
      exact hcne (Subsingleton.elim _ _)
    exact fun ⟨f⟩ => fourP_III_not_comm p hp2
      (fun a b => by
        have := nonabRep_comm_of_trivial p hc (f a) (f b)
        exact f.injective (by rw [map_mul, this, map_mul]))
  · have hp2 : p ≠ 2 := by
      intro h; subst h
      exact hc1 (Subsingleton.elim c 1)
    exact not_mulEquiv_of_orderOf
      (fourP_III_has_order_2p p hp hp2)
      (fourP_IV_no_order_2p p hp hp2 c hc hc1 hcne)

theorem fourP_III_ne_V (hp2 : p ≠ 2) :
    ¬ Nonempty (fourP_III p ≃* fourP_V p) := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hp1 : 2 < p := by
    have := (Fact.out (p := p.Prime)).two_le; omega
  exact not_mulEquiv_of_orderOf
    (nonabRep_has_order4 p (-1) (neg_one_pow_four_units p))
    (fourP_V_no_order4 p hp1 Fact.out)

theorem fourP_IV_ne_V (c : (ZMod p)ˣ) (hc : c ^ 4 = 1) (_ : c ≠ 1) (hp2 : p ≠ 2) :
    ¬ Nonempty (fourP_IV p c hc ≃* fourP_V p) := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hp := Fact.out (p := p.Prime)
  have hp1 : 2 < p := by have := hp.two_le; omega
  exact not_mulEquiv_of_orderOf
    (nonabRep_has_order4 p c hc)
    (fourP_V_no_order4 p hp1 hp)

/-! ### Exhaustiveness (4 classes, p ≡ 3 mod 4, p > 3) -/

/-- In `(ZMod p)ˣ` for p prime, `u² = 1` implies `u = 1` or `u = -1`. -/
private theorem units_sq_eq_one_of_prime {p : ℕ} [Fact p.Prime]
    (u : (ZMod p)ˣ) (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  haveI : NeZero p := NeZero.of_pos (Fact.out (p := p.Prime)).pos
  have h1 : (u.val : ZMod p) ^ 2 = 1 := by
    have := congrArg (fun x => (x.val : ZMod p)) hu
    simpa [Units.val_pow_eq_pow_val] using this
  have h : ((u : ZMod p) - 1) * ((u : ZMod p) + 1) = 0 := by
    have h2 : (u : ZMod p) ^ 2 - 1 = 0 := sub_eq_zero.mpr h1
    linear_combination h2
  rcases mul_eq_zero.mp h with h1 | h2
  · left; ext; simpa using sub_eq_zero.mp h1
  · right; ext; simpa using add_eq_zero_iff_eq_neg.mp h2

private theorem not_dvd_p_sub_one_of_mod_four_three {p : ℕ} (hmod : p % 4 = 3) : ¬ 4 ∣ p - 1 := by
  omega

private theorem units_pow_four_eq_one_iff {p : ℕ} [Fact p.Prime] (hmod : p % 4 = 3) (u : (ZMod p)ˣ)
    (hu : u ^ 4 = 1) : u = 1 ∨ u = -1 := by
  have hp_prime := Fact.out (p := p.Prime)
  haveI : NeZero p := NeZero.of_pos hp_prime.pos
  have h_neg1_ne_one : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have h_eq_mod : (-1 : ZMod p) = (1 : ZMod p) := by
      simpa using congrArg Units.val h
    have h2 : (2 : ZMod p) = 0 := by
      calc
        (2 : ZMod p) = (1 : ZMod p) - (-1 : ZMod p) := by ring
        _ = (1 : ZMod p) - (1 : ZMod p) := by rw [h_eq_mod]
        _ = 0 := by ring
    have hp_dvd_2 : p ∣ 2 := ((ZMod.natCast_eq_zero_iff 2 p).mp h2)
    have h_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd_2
    have := hp_prime.two_le
    omega
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  · by_cases hun1 : u = -1
    · exact Or.inr hun1
    · have hsq : u ^ 2 = -1 := sq_eq_neg_one_of_pow_four (p := p) u hu hu1 hun1
      have h_dvd_4 : orderOf u ∣ 4 := by
        rw [orderOf_dvd_iff_pow_eq_one]; exact hu
      have h_ne_1 : orderOf u ≠ 1 := mt orderOf_eq_one_iff.mp hu1
      have h_ne_2 : orderOf u ≠ 2 := by
        intro h_eq2
        have h2 : u ^ 2 = 1 := by rw [← h_eq2]; exact pow_orderOf_eq_one u
        rw [hsq] at h2
        exact h_neg1_ne_one h2
      have hord : orderOf u = 4 := by
        have h_pos : 0 < orderOf u := orderOf_pos u
        have h_le : orderOf u ≤ 4 := Nat.le_of_dvd (by norm_num) h_dvd_4
        have h_cases : orderOf u = 1 ∨ orderOf u = 2 ∨ orderOf u = 3 ∨ orderOf u = 4 := by
          omega
        rcases h_cases with (h | h | h | h)
        · exact absurd h h_ne_1
        · exact absurd h h_ne_2
        · rw [h] at h_dvd_4; norm_num at h_dvd_4
        · exact h
      have h_dvd_card : orderOf u ∣ Fintype.card ((ZMod p)ˣ) := orderOf_dvd_card
      rw [hord] at h_dvd_card
      have h_card : Fintype.card ((ZMod p)ˣ) = p - 1 :=
        ZMod.card_units p
      rw [h_card] at h_dvd_card
      have h_not_4_dvd : ¬ 4 ∣ p - 1 := not_dvd_p_sub_one_of_mod_four_three hmod
      exact absurd h_dvd_card h_not_4_dvd

private theorem mulEquiv_eq_unitAutHom (σ : MulAut (Multiplicative (ZMod p))) :
    ∃ u : (ZMod p)ˣ, σ = unitAutHom u := by
  let u_val : ZMod p := (σ (Multiplicative.ofAdd (1 : ZMod p))).toAdd
  have hu_ne_zero : u_val ≠ 0 := by
    intro hz
    have h0 : σ (Multiplicative.ofAdd (0 : ZMod p)) = Multiplicative.ofAdd (0 : ZMod p) := by
      calc
        σ (Multiplicative.ofAdd (0 : ZMod p)) = σ 1 := by simp
        _ = 1 := map_one σ
        _ = Multiplicative.ofAdd (0 : ZMod p) := by simp
    have h1 : σ (Multiplicative.ofAdd (1 : ZMod p)) = Multiplicative.ofAdd (0 : ZMod p) := by
      calc
        σ (Multiplicative.ofAdd (1 : ZMod p)) = Multiplicative.ofAdd u_val := rfl
        _ = Multiplicative.ofAdd (0 : ZMod p) := by rw [hz]
    have h01 : Multiplicative.ofAdd (0 : ZMod p) ≠ Multiplicative.ofAdd (1 : ZMod p) := by
      intro h
      apply_fun Multiplicative.toAdd at h
      simp at h
    apply h01
    exact σ.injective (h0.trans h1.symm)
  have h_inv : u_val⁻¹ * u_val = 1 := by field_simp [hu_ne_zero]
  have h_mul : u_val * u_val⁻¹ = 1 := by field_simp [hu_ne_zero]
  let u : (ZMod p)ˣ := Units.mk u_val (u_val⁻¹) h_mul h_inv
  refine ⟨u, ?_⟩
  apply MulEquiv.ext
  intro x
  let n := Multiplicative.toAdd x
  have hx : Multiplicative.ofAdd n = x := by
    exact ofAdd_toAdd x
  rw [← hx]
  calc
    σ (Multiplicative.ofAdd n) = σ ((Multiplicative.ofAdd (1 : ZMod p)) ^ n.val) := by
      rw [show (Multiplicative.ofAdd n : Multiplicative (ZMod p)) =
          (Multiplicative.ofAdd (1 : ZMod p)) ^ n.val from by
        calc
          Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod p)) := by
            rw [ZMod.natCast_zmod_val]
          _ = Multiplicative.ofAdd (n.val • (1 : ZMod p)) := by simp
          _ = (Multiplicative.ofAdd (1 : ZMod p)) ^ n.val := by
            rw [ofAdd_nsmul]
      ]
    _ = (σ (Multiplicative.ofAdd (1 : ZMod p))) ^ n.val := by rw [map_pow]
    _ = (Multiplicative.ofAdd u_val) ^ n.val := rfl
    _ = Multiplicative.ofAdd (n.val • u_val) := by
      rw [← ofAdd_nsmul]
    _ = Multiplicative.ofAdd (u_val * (n.val : ZMod p)) := by
      rw [nsmul_eq_mul, mul_comm]
    _ = Multiplicative.ofAdd (u_val * n) := by rw [ZMod.natCast_zmod_val]
    _ = unitAutHom u (Multiplicative.ofAdd n) := by
      rw [unitAutHom_apply]

private theorem action_trivial_of_abelian {N H : Type*} [Group N] [Group H]
    (φ : H →* MulAut N) (hcomm : ∀ a b : SemidirectProduct N H φ, a * b = b * a) :
    φ = 1 := by
  ext h n
  have h_comm := hcomm (SemidirectProduct.inr h) (SemidirectProduct.inl n)
  have h_left := congrArg (·.left) h_comm
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one, one_mul] at h_left
  simpa using h_left


/-- Core of the mod-3 classification: given a non-cyclic group of order `4p` with a
semidirect product decomposition, classifies the group as one of the four types.
Does NOT require `5 ≤ p`, only `p.Prime` and `p ≠ 2`. -/
theorem fourP_classification_mod3_aux {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : p % 4 = 3) {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 4 * p) (hcyc : ¬ IsCyclic G)
    (N H : Subgroup G) (φ : H →* MulAut N)
    (hcardN : Nat.card N = p) (hcardH : Nat.card H = 4)
    (e : G ≃* SemidirectProduct N H φ) :
    Nonempty (G ≃* fourP_I p) ∨
    Nonempty (G ≃* fourP_II p) ∨
    Nonempty (G ≃* fourP_III p) ∨
    Nonempty (G ≃* fourP_V p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_two_le : 2 ≤ p := hp.two_le
  have hiN : Nonempty (N ≃* Multiplicative (ZMod p)) := prime_classification hp hcardN
  have hp_cop_2 : Nat.Coprime 2 p :=
    Nat.prime_two.coprime_iff_not_dvd.mpr fun h =>
      have := hp.eq_one_or_self_of_dvd 2 h
      this.elim (fun h1 => by omega) (fun h2 => hp2 h2.symm)
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hcardH_sq : Nat.card H = 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hcardH]
  rcases prime_sq_classification (p := 2) hcardH_sq with (hHcyc | hHk4)
  · -- H ≅ C₄
    obtain ⟨iH_cyc⟩ := hHcyc
    have iH : H ≃* Multiplicative (ZMod 4) := by simpa [CyclicRep] using iH_cyc
    obtain ⟨iN⟩ := hiN
    have hN_cyc : IsCyclic N := isCyclic_of_card_eq_prime hp hcardN
    have hh₀_ord : orderOf (iH.symm (Multiplicative.ofAdd (1 : ZMod 4))) = 4 := by
      rw [MulEquiv.orderOf_eq iH.symm, orderOf_ofAdd_eq_addOrderOf,
        ZMod.addOrderOf_one 4]
    have hn₀_ord : orderOf (iN.symm (Multiplicative.ofAdd (1 : ZMod p))) = p := by
      haveI : NeZero p := ⟨hp.ne_zero⟩
      rw [MulEquiv.orderOf_eq iN.symm, orderOf_ofAdd_eq_addOrderOf,
        ZMod.addOrderOf_one p]
    set h₀ := iH.symm (Multiplicative.ofAdd (1 : ZMod 4)) with hh₀_def
    set n₀ := iN.symm (Multiplicative.ofAdd (1 : ZMod p)) with hn₀_def
    by_cases hcomm : ∀ a b : G, a * b = b * a
    · -- Abelian C₄: φ trivial → G ≅ N×H ≅ Z/p×C₄ ≅ Z/(4p) → cyclic, contradiction with hcyc
      haveI : CommGroup G := { mul_comm := hcomm }
      have h_sd_comm : ∀ a b : SemidirectProduct N H φ, a * b = b * a := by
        intro a b
        have h_eq := hcomm (e.symm a) (e.symm b)
        apply_fun e at h_eq
        simpa [map_mul e, MulEquiv.apply_symm_apply] using h_eq
      have hφ : φ = 1 := action_trivial_of_abelian φ h_sd_comm
      subst hφ
      have hH_cyc : IsCyclic H :=
        iH.isCyclic.mpr inferInstance
      have h_cop : (Nat.card N).Coprime (Nat.card H) := by
        rw [hcardN, hcardH]
        have htemp := (Nat.coprime_pow_right_iff (by norm_num : 0 < 2) p 2).mpr hp_cop_2.symm
        simpa [show (2 : ℕ) ^ 2 = 4 by norm_num] using htemp
      have h_prod_cyc : IsCyclic (N × H) :=
        (Group.isCyclic_prod_iff.2 ⟨hN_cyc, hH_cyc, h_cop⟩)
      have hG_cyc : IsCyclic G :=
        isCyclic_of_surjective ((e.trans SemidirectProduct.mulEquivProd).symm.toMonoidHom)
          (MulEquiv.surjective _)
      exact absurd hG_cyc hcyc
    · -- Non-abelian C₄ → Type III
      have hh₀4 : h₀ ^ 4 = 1 := by
        rw [← hh₀_ord]; exact pow_orderOf_eq_one h₀
      have hφh₀4 : (φ h₀) ^ 4 = 1 := by
        rw [← map_pow, hh₀4, map_one]
      -- Conjugate φ h₀ by iN to get an automorphism of Multiplicative (ZMod p)
      let ψ : MulAut (Multiplicative (ZMod p)) :=
        (iN.symm.trans (φ h₀)).trans iN
      let conj_iN : MulAut N →* MulAut (Multiplicative (ZMod p)) :=
        { toFun := fun σ => (iN.symm.trans σ).trans iN
          map_one' := by ext x; simp
          map_mul' := fun σ τ => by ext x; simp }
      have hψ_eq : ψ = conj_iN (φ h₀) := rfl
      have h_ord_ψ : orderOf ψ ∣ 4 := by
        rw [hψ_eq]
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow, hφh₀4, map_one]
      obtain ⟨u, hu⟩ := mulEquiv_eq_unitAutHom (p := p) ψ
      have hu4 : u ^ 4 = 1 := by
        have hinj : Function.Injective (unitAutHom (p := p)) := by
          intro u v h
          have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod p)) =
                   unitAutHom v (Multiplicative.ofAdd (1 : ZMod p)) := by rw [h]
          simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
          apply Units.ext
          exact congrArg Multiplicative.toAdd h1
        have h_ord_u : orderOf u ∣ 4 := by
          have h_eq : orderOf (unitAutHom u) = orderOf u :=
            orderOf_injective (unitAutHom (p := p)) hinj u
          rw [← h_eq, ← hu]
          exact h_ord_ψ
        apply (orderOf_dvd_iff_pow_eq_one (x := u) (n := 4)).mp
        exact h_ord_u
      have hu_cases := units_pow_four_eq_one_iff hmod u hu4
      rcases hu_cases with (hu1 | hun1)
      · -- u = 1, so ψ = 1, so φ h₀ = 1
        have hψ1 : ψ = 1 := by rw [hu, hu1, map_one]
        have hφh₀1 : φ h₀ = 1 := by
          apply MulEquiv.ext; intro n
          apply iN.injective
          have hψ1_eq : ∀ x, ψ x = x := by rw [hψ1]; simp
          have htemp := hψ1_eq (iN n)
          dsimp [ψ] at htemp
          simpa using htemp
        -- h₀ generates H since orderOf h₀ = 4 = card H
        have hgen : ∀ h : H, h ∈ Subgroup.zpowers h₀ := by
          have hcz : Nat.card (Subgroup.zpowers h₀ : Subgroup H) = Nat.card H := by
            rw [Nat.card_zpowers, hh₀_ord, hcardH]
          have hz_eq : Subgroup.zpowers h₀ = ⊤ :=
            Subgroup.eq_top_of_card_eq _ hcz
          intro h; rw [hz_eq]; trivial
        have hφ1 : φ = 1 := by
          ext h n
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen h)
          have hφh_eq_one : φ h = 1 := by
            calc
              φ h = φ (h₀ ^ k) := by rw [hk]
              _ = (φ h₀) ^ k := by rw [map_zpow]
              _ = 1 ^ k := by rw [hφh₀1]
              _ = 1 := by simp
          simp [hφh_eq_one]
        -- φ = 1 implies SemidirectProduct is direct product, which is abelian
        have h_sd_comm : ∀ a b : SemidirectProduct N H φ, a * b = b * a := by
          rw [hφ1]
          intro a b
          apply (SemidirectProduct.mulEquivProd).injective
          have hN_comm : ∀ n1 n2 : N, n1 * n2 = n2 * n1 := by
            intro n1 n2; apply iN.injective; simp [mul_comm]
          have hH_comm : ∀ h1 h2 : H, h1 * h2 = h2 * h1 := by
            intro h1 h2; apply iH.injective; simp [mul_comm]
          simp only [map_mul, SemidirectProduct.mulEquivProd_apply]
          simp [hN_comm a.left b.left, hH_comm a.right b.right]
        have hG_comm : ∀ a b : G, a * b = b * a := by
          intro a b
          have h_eq := h_sd_comm (e a) (e b)
          apply_fun e.symm at h_eq
          simpa using h_eq
        exact absurd hG_comm hcomm
      · -- u = -1, so ψ = unitAutHom (-1) acts as inversion
        -- Then φ h₀ n₀ = n₀⁻¹
        have hψ_eq : ψ = unitAutHom (-1) := by rw [hu, hun1]
        have hφh₀_inv : ∀ n : N, φ h₀ n = n⁻¹ := by
          intro n
          apply iN.injective
          calc
            iN (φ h₀ n) = ψ (iN n) := by dsimp [ψ]; simp
            _ = unitAutHom (-1) (iN n) := by rw [hψ_eq]
            _ = (iN n)⁻¹ := by
              let m := Multiplicative.toAdd (iN n)
              have hm : iN n = Multiplicative.ofAdd m :=
                (ofAdd_toAdd _).symm
              rw [hm]
              simp [unitAutHom_apply]
            _ = iN (n⁻¹) := by simp
        -- Now construct a, b in G and apply nonempty_mulEquiv_nonabRep
        set a := e.symm (SemidirectProduct.inl n₀) with ha_def
        set b := e.symm (SemidirectProduct.inr h₀) with hb_def
        have ha : orderOf a = p := by
          rw [ha_def, MulEquiv.orderOf_eq e.symm,
            orderOf_injective (SemidirectProduct.inl : N →* SemidirectProduct N H φ)
              SemidirectProduct.inl_injective n₀, hn₀_ord]
        have hb : orderOf b = 4 := by
          rw [hb_def, MulEquiv.orderOf_eq e.symm,
            orderOf_injective (SemidirectProduct.inr : H →* SemidirectProduct N H φ)
              SemidirectProduct.inr_injective h₀, hh₀_ord]
        have ha_pow_p : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
        have ha_inv_eq_pow_sub : a⁻¹ = a ^ (p - 1) := by
          apply (eq_inv_of_mul_eq_one_left ?_).symm
          calc
            a ^ (p - 1) * a = a ^ ((p - 1) + 1) := by rw [pow_succ]
            _ = a ^ p := by rw [Nat.sub_add_cancel (by omega : 1 ≤ p)]
            _ = 1 := ha_pow_p
        have h_val_neg_one : ((-1 : (ZMod p)ˣ).val : ZMod p).val = p - 1 := by
          have hp_eq : ((p - 1 : ℕ).succ : ℕ) = p := by omega
          have htemp : ((-1 : (ZMod p)ˣ).val : ZMod p) = (-1 : ZMod p) := by simp
          rw [htemp]
          have h := ZMod.val_neg_one (p - 1)
          rw [hp_eq] at h
          simpa using h
        have hconj : b * a * b⁻¹ = a ^ (((-1 : (ZMod p)ˣ).val : ZMod p).val) := by
          calc
            b * a * b⁻¹ = e.symm (SemidirectProduct.inr h₀ * SemidirectProduct.inl n₀ *
              (SemidirectProduct.inr h₀)⁻¹) := by simp [ha_def, hb_def]
            _ = e.symm (SemidirectProduct.inl (φ h₀ n₀)) := by
              simp [SemidirectProduct.inl_aut]
            _ = e.symm (SemidirectProduct.inl (n₀⁻¹)) := by rw [hφh₀_inv n₀]
            _ = e.symm ((SemidirectProduct.inl n₀)⁻¹) := by simp
            _ = a⁻¹ := by simp [ha_def]
            _ = a ^ (p - 1) := by rw [ha_inv_eq_pow_sub]
            _ = a ^ (((-1 : (ZMod p)ˣ).val : ZMod p).val) := by rw [h_val_neg_one]
        have hcop : Nat.Coprime p 4 := by
          have htemp := (Nat.coprime_pow_right_iff (by norm_num : 0 < 2) p 2).mpr hp_cop_2.symm
          simpa [show (2 : ℕ) ^ 2 = 4 by norm_num] using htemp
        have hcardG : Nat.card G = p * 4 := by
          rw [hG]; ring
        haveI : NeZero p := ⟨hp.ne_zero⟩
        haveI : NeZero 4 := ⟨by norm_num⟩
        have h_nonab : Nonempty (G ≃* NonabRep (-1 : (ZMod p)ˣ) (neg_one_pow_four_units p)) :=
          nonempty_mulEquiv_nonabRep a b ha hb (-1 : (ZMod p)ˣ) (neg_one_pow_four_units p)
            hconj hcop hcardG
        right; right; left
        simpa [fourP_III] using h_nonab
  · -- H ≅ K₄
    by_cases hcomm : ∀ a b : G, a * b = b * a
    · -- Abelian K₄ → Type II: G ≅ Z/2 × Z/(2p) = fourP_II p
      haveI : CommGroup G := { mul_comm := hcomm }
      have h_sd_comm : ∀ a b : SemidirectProduct N H φ, a * b = b * a := by
        intro a b
        have h_eq := hcomm (e.symm a) (e.symm b)
        apply_fun e at h_eq
        simpa [map_mul e, MulEquiv.apply_symm_apply] using h_eq
      have hφ : φ = 1 := action_trivial_of_abelian φ h_sd_comm
      subst hφ
      -- G ≃* N × H via SemidirectProduct.mulEquivProd
      have hG_NH : Nonempty (G ≃* (N × H)) :=
        ⟨e.trans SemidirectProduct.mulEquivProd⟩
      obtain ⟨eG_NH⟩ := hG_NH
      -- N ≅ Z/p, H ≅ Z/2 × Z/2
      obtain ⟨iN⟩ := hiN
      obtain ⟨iH⟩ := hHk4
      let iH' : H ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
        simpa [ElemAbelianRep, CyclicRep] using iH
      right; left
      let A := Multiplicative (ZMod p)
      let B := Multiplicative (ZMod 2)
      let C := Multiplicative (ZMod 2)
      let D := Multiplicative (ZMod (2 * p))
      have h_crt : C × A ≃* D := crtProd 2 p hp_cop_2
      have h_prod_iso : (N × H) ≃* (B × D) :=
        let e1 := MulEquiv.prodCongr iN iH'
        let e2 := (MulEquiv.prodAssoc (M := A) (N := B) (P := C)).symm
        let e3 := MulEquiv.prodCongr (MulEquiv.prodComm (M := A) (N := B))
          (MulEquiv.refl (M := C))
        let e4 := MulEquiv.prodAssoc (M := B) (N := A) (P := C)
        let e5 := MulEquiv.prodCongr (MulEquiv.refl (M := B))
          (MulEquiv.prodComm (M := A) (N := C))
        let e6 := MulEquiv.prodCongr (MulEquiv.refl (M := B)) h_crt
        (e1.trans e2).trans e3 |>.trans e4 |>.trans e5 |>.trans e6
      refine ⟨eG_NH.trans h_prod_iso⟩
    · -- Non-abelian K₄ → Type V: G ≅ ℤ/2 × D_{2p}
      -- Each generator of K₄ acts on N ≅ ℤ/p by ±1.
      -- Since G non-abelian, at least one acts by -1.
      -- If both act by -1, replace one generator to get one trivial / one inversion.
      -- Result: G ≅ ℤ/2 × D_{2p}.
      obtain ⟨iN⟩ := hiN
      obtain ⟨iH⟩ := hHk4
      let iH' : H ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
        simpa [ElemAbelianRep, CyclicRep] using iH
      -- generators of H
      set u₁ := iH'.symm (Multiplicative.ofAdd 1, 1) with hu₁_def
      set u₂ := iH'.symm (1, Multiplicative.ofAdd 1) with hu₂_def
      have hzmod2_add : (1 : ZMod 2) + 1 = 0 := by
        have h2 : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
        calc (1 : ZMod 2) + 1 = 2 := by ring
          _ = 0 := h2
      have hu₁_sq : u₁ ^ 2 = 1 := by
        have h : iH' u₁ = (Multiplicative.ofAdd 1, (1 : Multiplicative (ZMod 2))) :=
          MulEquiv.apply_symm_apply iH' _
        apply iH'.injective; simp only [map_pow, map_one, h]
        ext <;> simp [sq, hzmod2_add]
      have hu₂_sq : u₂ ^ 2 = 1 := by
        have h : iH' u₂ = ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd 1) :=
          MulEquiv.apply_symm_apply iH' _
        apply iH'.injective; simp only [map_pow, map_one, h]
        ext <;> simp [sq, hzmod2_add]
      -- φ(u₁)² = 1 and φ(u₂)² = 1 in Aut(N)
      have hφu₁_sq : (φ u₁) ^ 2 = 1 := by rw [← map_pow, hu₁_sq, map_one]
      have hφu₂_sq : (φ u₂) ^ 2 = 1 := by rw [← map_pow, hu₂_sq, map_one]
      -- Conjugate to automorphisms of Multiplicative (ZMod p)
      let ψ₁ := (iN.symm.trans (φ u₁)).trans iN
      let ψ₂ := (iN.symm.trans (φ u₂)).trans iN
      have hψ₁_sq : ψ₁ ^ 2 = 1 := by
        have key : ∀ n : N, ψ₁ (ψ₁ (iN n)) = iN n := by
          intro n; dsimp only [ψ₁, MulEquiv.trans_apply]
          simp only [MulEquiv.symm_apply_apply]
          congr 1
          rw [← MulAut.mul_apply, ← sq, hφu₁_sq, MulAut.one_apply]
        ext x
        obtain ⟨n, rfl⟩ := iN.surjective x
        simp only [MulAut.one_apply, pow_succ, pow_zero, MulAut.mul_apply, key]
      have hψ₂_sq : ψ₂ ^ 2 = 1 := by
        have key : ∀ n : N, ψ₂ (ψ₂ (iN n)) = iN n := by
          intro n; dsimp only [ψ₂, MulEquiv.trans_apply]
          simp only [MulEquiv.symm_apply_apply]
          congr 1
          rw [← MulAut.mul_apply, ← sq, hφu₂_sq, MulAut.one_apply]
        ext x
        obtain ⟨n, rfl⟩ := iN.surjective x
        simp only [MulAut.one_apply, pow_succ, pow_zero, MulAut.mul_apply, key]
      -- Each ψᵢ = unitAutHom(uᵢ) for some unit uᵢ with uᵢ² = 1
      obtain ⟨v₁, hv₁⟩ := mulEquiv_eq_unitAutHom (p := p) ψ₁
      obtain ⟨v₂, hv₂⟩ := mulEquiv_eq_unitAutHom (p := p) ψ₂
      have hv₁_sq : v₁ ^ 2 = 1 := by
        have hinj : Function.Injective (unitAutHom (p := p)) := by
          intro u v h
          have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod p)) =
                   unitAutHom v (Multiplicative.ofAdd (1 : ZMod p)) := by rw [h]
          simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
          exact Units.ext (congrArg Multiplicative.toAdd h1)
        have := hinj (by rw [map_pow, ← hv₁, hψ₁_sq, map_one] :
          unitAutHom (v₁ ^ 2) = unitAutHom 1)
        exact this
      have hv₂_sq : v₂ ^ 2 = 1 := by
        have hinj : Function.Injective (unitAutHom (p := p)) := by
          intro u v h
          have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod p)) =
                   unitAutHom v (Multiplicative.ofAdd (1 : ZMod p)) := by rw [h]
          simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
          exact Units.ext (congrArg Multiplicative.toAdd h1)
        have := hinj (by rw [map_pow, ← hv₂, hψ₂_sq, map_one] :
          unitAutHom (v₂ ^ 2) = unitAutHom 1)
        exact this
      -- v₁, v₂ ∈ {1, -1} since x² = 1 in (ZMod p)ˣ iff x = ±1
      have hv₁_cases : v₁ = 1 ∨ v₁ = -1 :=
        units_sq_eq_one_of_prime v₁ hv₁_sq
      have hv₂_cases : v₂ = 1 ∨ v₂ = -1 :=
        units_sq_eq_one_of_prime v₂ hv₂_sq
      -- φ(u) acts by inversion when the corresponding unit is -1
      have unitAutHom_neg1_inv : ∀ x : Multiplicative (ZMod p),
          unitAutHom (-1 : (ZMod p)ˣ) x = x⁻¹ := by
        intro x
        let m := Multiplicative.toAdd x
        have hm : x = Multiplicative.ofAdd m := (ofAdd_toAdd _).symm
        rw [hm]; simp [unitAutHom_apply]
      have hφ_inv_of_neg1 : ∀ (u : H) (v : (ZMod p)ˣ),
          (iN.symm.trans (φ u)).trans iN = unitAutHom v → v = -1 →
          ∀ n : N, φ u n = n⁻¹ := by
        intro u v hψ hv n
        apply iN.injective
        have h := MulEquiv.ext_iff.mp hψ (iN n)
        simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
        rw [h, hv, unitAutHom_neg1_inv]; simp
      have hφ_triv_of_1 : ∀ (u : H) (v : (ZMod p)ˣ),
          (iN.symm.trans (φ u)).trans iN = unitAutHom v → v = 1 →
          φ u = 1 := by
        intro u v hψ hv
        apply MulEquiv.ext; intro n
        have h := MulEquiv.ext_iff.mp hψ (iN n)
        simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
        have h2 : iN ((φ u) n) = iN n := by
          rw [h, hv]; simp
        exact iN.injective h2
      -- Since G is non-abelian, φ ≠ 1. So at least one of v₁, v₂ is -1.
      -- Find h_inv (inverts N) and h_triv (acts trivially).
      -- If both invert: u₁u₂ acts trivially, so use h_inv = u₁, h_triv = u₁ * u₂.
      -- Product u₁ * u₂ in H maps to (ofAdd 1, ofAdd 1) in K₄.
      have hu₁u₂ : iH' (u₁ * u₂) = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) := by
        simp [hu₁_def, hu₂_def, map_mul, MulEquiv.apply_symm_apply]
      have hu₁_comm_u₂ : Commute u₁ u₂ := by
        change u₁ * u₂ = u₂ * u₁
        apply iH'.injective; simp [map_mul, mul_comm]
      have hu₁u₂_sq : (u₁ * u₂) ^ 2 = 1 := by
        rw [hu₁_comm_u₂.mul_pow, hu₁_sq, hu₂_sq, one_mul]
      have hφu₁u₂ : φ (u₁ * u₂) = φ u₁ * φ u₂ := map_mul φ u₁ u₂
      -- Obtain h_inv (inverts) and h_triv (trivial), both order 2, h_triv ≠ 1
      obtain ⟨h_inv, h_triv, hφ_inv, hφ_triv, h_inv_sq, h_triv_sq, h_triv_ne_1⟩ :
          ∃ (h_inv h_triv : H),
            (∀ n : N, φ h_inv n = n⁻¹) ∧ (φ h_triv = 1) ∧
            h_inv ^ 2 = 1 ∧ h_triv ^ 2 = 1 ∧ h_triv ≠ 1 := by
        rcases hv₁_cases with hv₁1 | hv₁neg1 <;> rcases hv₂_cases with hv₂1 | hv₂neg1
        · -- v₁ = 1, v₂ = 1: both trivial → φ = 1 → G abelian, contradiction
          exfalso; apply hcomm
          have hφu₁_1 := hφ_triv_of_1 u₁ v₁ hv₁ hv₁1
          have hφu₂_1 := hφ_triv_of_1 u₂ v₂ hv₂ hv₂1
          -- φ u = 1 for all u since u₁, u₂ generate H
          have hφ_all : ∀ h : H, φ h = 1 := by
            intro h
            have hu₁_im : iH' u₁ = (Multiplicative.ofAdd 1, 1) :=
              MulEquiv.apply_symm_apply iH' _
            have hu₂_im : iH' u₂ = (1, Multiplicative.ofAdd 1) :=
              MulEquiv.apply_symm_apply iH' _
            have hh_decomp : h = u₁ ^ (Multiplicative.toAdd (iH' h).1).val *
                u₂ ^ (Multiplicative.toAdd (iH' h).2).val := by
              apply iH'.injective
              rw [map_mul, map_pow, map_pow, hu₁_im, hu₂_im]
              ext
              · simp
              · simp
            rw [hh_decomp, map_mul, map_pow, map_pow, hφu₁_1, hφu₂_1]; simp
          have hφ1 : φ = 1 := by
            ext h n; have := hφ_all h; simp [this]
          -- φ = 1 → semidirect product is abelian → G is abelian
          have h_sd_comm : ∀ a b : SemidirectProduct N H φ, a * b = b * a := by
            intro a b
            have hl : a.left * b.left = b.left * a.left := by
              apply iN.injective; simp [mul_comm]
            have hr : a.right * b.right = b.right * a.right := by
              apply iH'.injective; simp [mul_comm]
            apply SemidirectProduct.ext
            · simp [SemidirectProduct.mul_left, hφ_all, hl]
            · simp [SemidirectProduct.mul_right, hr]
          intro x y
          have := h_sd_comm (e x) (e y)
          apply_fun e.symm at this; simpa using this
        · -- v₁ = 1, v₂ = -1
          have hu₁_ne_1 : u₁ ≠ 1 := by
            intro h; have := congrArg iH' h; simp [hu₁_def] at this
          exact ⟨u₂, u₁, hφ_inv_of_neg1 u₂ v₂ hv₂ hv₂neg1,
            hφ_triv_of_1 u₁ v₁ hv₁ hv₁1, hu₂_sq, hu₁_sq, hu₁_ne_1⟩
        · -- v₁ = -1, v₂ = 1
          have hu₂_ne_1 : u₂ ≠ 1 := by
            intro h; have := congrArg iH' h; simp [hu₂_def] at this
          exact ⟨u₁, u₂, hφ_inv_of_neg1 u₁ v₁ hv₁ hv₁neg1,
            hφ_triv_of_1 u₂ v₂ hv₂ hv₂1, hu₁_sq, hu₂_sq, hu₂_ne_1⟩
        · -- v₁ = -1, v₂ = -1: u₁u₂ acts trivially
          have hφu₁u₂_triv : φ (u₁ * u₂) = 1 := by
            apply MulEquiv.ext; intro n
            rw [hφu₁u₂, MulAut.mul_apply,
              hφ_inv_of_neg1 u₂ v₂ hv₂ hv₂neg1 n,
              hφ_inv_of_neg1 u₁ v₁ hv₁ hv₁neg1 n⁻¹]
            simp
          have hu₁u₂_ne_1 : u₁ * u₂ ≠ 1 := by
            intro h; have := congrArg iH' h; simp [map_mul, hu₁_def, hu₂_def] at this
          exact ⟨u₁, u₁ * u₂, hφ_inv_of_neg1 u₁ v₁ hv₁ hv₁neg1,
            hφu₁u₂_triv, hu₁_sq, hu₁u₂_sq, hu₁u₂_ne_1⟩
      -- Now we have h_inv (inverts N) and h_triv (acts trivially), both order 2.
      -- Build elements in G.
      haveI : NeZero p := ⟨hp.ne_zero⟩
      set n₀ := iN.symm (Multiplicative.ofAdd (1 : ZMod p)) with hn₀_def
      have hn₀_ord : orderOf n₀ = p := by
        rw [MulEquiv.orderOf_eq iN.symm, orderOf_ofAdd_eq_addOrderOf,
          ZMod.addOrderOf_one p]
      set a := e.symm (SemidirectProduct.inl n₀) with ha_def
      set b := e.symm (SemidirectProduct.inr h_inv) with hb_def
      set z := e.symm (SemidirectProduct.inr h_triv) with hz_def
      -- orderOf a = p
      have ha_ord : orderOf a = p := by
        rw [ha_def, MulEquiv.orderOf_eq e.symm,
          orderOf_injective SemidirectProduct.inl
            SemidirectProduct.inl_injective n₀, hn₀_ord]
      -- b² = 1
      have hb_sq : b ^ 2 = 1 := by
        apply e.injective; simp only [hb_def, map_pow, map_one, MulEquiv.apply_symm_apply]
        rw [← map_pow]; simp [h_inv_sq]
      -- b ≠ 1 (since φ h_inv ≠ 1, the action is non-trivial)
      have hb_ne_1 : b ≠ 1 := by
        intro hb1
        -- φ h_inv is inversion but if b = 1, then h_inv = 1, so φ h_inv = 1
        have hinv1 : h_inv = 1 := by
          have hb1' := congrArg e hb1
          simp only [hb_def, MulEquiv.apply_symm_apply, map_one] at hb1'
          exact SemidirectProduct.inr_injective hb1'
        have hφ_hinv_1 : φ h_inv = 1 := by rw [hinv1, map_one]
        have h_n₀_sq : n₀ ^ 2 = 1 := by
          have h1 : n₀ = n₀⁻¹ := by
            have := hφ_inv n₀; rw [hφ_hinv_1] at this; simpa using this
          rw [sq]; conv_lhs => lhs; rw [h1]
          exact inv_mul_cancel n₀
        have h_ord_dvd : orderOf n₀ ∣ 2 := orderOf_dvd_of_pow_eq_one h_n₀_sq
        rw [hn₀_ord] at h_ord_dvd
        exact absurd (Nat.le_of_dvd (by norm_num) h_ord_dvd) (by omega)
      -- b * a * b⁻¹ = a⁻¹ (the dihedral relation)
      have hba_inv : b * a * b⁻¹ = a⁻¹ := by
        apply e.injective
        have heb : e b = SemidirectProduct.inr h_inv := by
          simp only [hb_def, MulEquiv.apply_symm_apply]
        have hea : e a = SemidirectProduct.inl n₀ := by
          simp only [ha_def, MulEquiv.apply_symm_apply]
        have lhs_eq : e (b * a * b⁻¹) = SemidirectProduct.inl (φ h_inv n₀) := by
          rw [map_mul, map_mul, map_inv, heb, hea]
          simp [SemidirectProduct.inl_aut]
        have rhs_eq : e (a⁻¹) = SemidirectProduct.inl (n₀⁻¹) := by
          rw [map_inv, hea, map_inv]
        rw [lhs_eq, rhs_eq, hφ_inv n₀]
      -- z² = 1
      have hz_sq : z ^ 2 = 1 := by
        apply e.injective; simp only [hz_def, map_pow, map_one, MulEquiv.apply_symm_apply]
        rw [← map_pow]; simp [h_triv_sq]
      -- z commutes with a
      have hza : z * a = a * z := by
        apply e.injective
        rw [map_mul, map_mul]
        simp only [ha_def, hz_def, MulEquiv.apply_symm_apply]
        apply SemidirectProduct.ext
        · simp [SemidirectProduct.mul_left, hφ_triv]
        · simp [SemidirectProduct.mul_right]
      -- z commutes with b (both come from H, which is abelian)
      have hzb : z * b = b * z := by
        apply e.injective
        rw [map_mul, map_mul]
        simp only [hb_def, hz_def, MulEquiv.apply_symm_apply]
        rw [← map_mul, ← map_mul]
        congr 1
        apply iH'.injective; simp [map_mul, mul_comm]
      -- Now build the isomorphism G ≃* Multiplicative (ZMod 2) × DihedralGroup p
      -- Use nonempty_mulEquiv_dihedral to get ⟨a, b⟩ → D_{2p} on a subgroup,
      -- then extend with z.
      -- Build the map fourP_V p → G
      have ha_pow_p : a ^ p = 1 := by rw [← ha_ord]; exact pow_orderOf_eq_one a
      have hodd : Odd p := hp.odd_of_ne_two (by omega)
      -- The map DihedralGroup p → G sending r i ↦ a^i.val, sr i ↦ b * a^i.val
      -- is a MonoidHom (reuse infrastructure from PrimePairDihedral)
      -- Combined map: (j, d) ↦ z^j.val * f_dih(d)
      -- where f_dih : DihedralGroup p → G is the dihedral embedding
      -- First build f_dih using the same approach as nonempty_mulEquiv_dihedral
      have hab : a * b = b * a⁻¹ := by
        have h2 : b * a = a⁻¹ * b := by rw [← hba_inv]; group
        calc a * b = a * b * a * a⁻¹ := by group
          _ = a * (a⁻¹ * b) * a⁻¹ := by rw [← h2]; group
          _ = b * a⁻¹ := by group
      have hak : ∀ k : ℕ, a ^ k * b = b * (a⁻¹) ^ k := by
        intro k; induction k with
        | zero => simp
        | succ n ih => rw [pow_succ, mul_assoc, hab, ← mul_assoc, ih, mul_assoc, ← pow_succ]
      have hbb : b * b = 1 := by rw [← pow_two]; exact hb_sq
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
      have hcom : ∀ m n : ℕ, (a ^ m)⁻¹ * a ^ n = a ^ n * (a ^ m)⁻¹ :=
        fun m n => ((((Commute.refl a).pow_pow n m).inv_right).eq).symm
      have hc_add : ∀ i j : ZMod p, a ^ (i + j).val = a ^ i.val * a ^ j.val := by
        intro i j; rw [← pow_add]; apply pow_eq_pow_iff_modEq.mpr
        rw [ha_ord, ZMod.val_add]; exact Nat.mod_modEq _ _
      have hc_sub : ∀ i j : ZMod p, a ^ (j - i).val = a ^ j.val * (a ^ i.val)⁻¹ := by
        intro i j; have h := hc_add (j - i) i
        rw [sub_add_cancel] at h; exact eq_mul_inv_iff_mul_eq.mpr h.symm
      have hrsr : ∀ m n : ℕ, a ^ m * (b * a ^ n) = b * (a ^ n * (a ^ m)⁻¹) := by
        intro m n; rw [← mul_assoc, hak, mul_assoc, inv_pow, hcom]
      have hsrsr : ∀ m n : ℕ, b * a ^ m * (b * a ^ n) = a ^ n * (a ^ m)⁻¹ := by
        intro m n; rw [mul_assoc, hrsr, ← mul_assoc, ← pow_two, hb_sq, one_mul]
      let f_dih_fn : DihedralGroup p → G := fun x => match x with
        | .r i => a ^ i.val
        | .sr i => b * a ^ i.val
      have hf_dih_mul : ∀ x y, f_dih_fn (x * y) = f_dih_fn x * f_dih_fn y := by
        rintro (i | i) (j | j)
        · exact hc_add i j
        · change b * a ^ (j - i).val = a ^ i.val * (b * a ^ j.val)
          rw [hc_sub, hrsr]
        · change b * a ^ (i + j).val = b * a ^ i.val * a ^ j.val
          rw [hc_add, mul_assoc]
        · change a ^ (j - i).val = b * a ^ i.val * (b * a ^ j.val)
          rw [hc_sub, hsrsr]
      let f_dih : DihedralGroup p →* G := MonoidHom.mk' f_dih_fn hf_dih_mul
      -- z commutes with everything in range of f_dih
      have hza_pow : ∀ k : ℕ, z * a ^ k = a ^ k * z := by
        intro k; induction k with
        | zero => simp
        | succ n ih =>
          calc z * a ^ (n + 1) = z * (a ^ n * a) := by rw [pow_succ]
            _ = (z * a ^ n) * a := by rw [mul_assoc]
            _ = (a ^ n * z) * a := by rw [ih]
            _ = a ^ n * (z * a) := by rw [mul_assoc]
            _ = a ^ n * (a * z) := by rw [hza]
            _ = a ^ (n + 1) * z := by rw [← mul_assoc, ← pow_succ]
      have hz_comm_dih : ∀ d : DihedralGroup p, z * f_dih d = f_dih d * z := by
        rintro (i | i)
        · exact hza_pow i.val
        · change z * (b * a ^ i.val) = (b * a ^ i.val) * z
          calc z * (b * a ^ i.val) = (z * b) * a ^ i.val := by rw [mul_assoc]
            _ = (b * z) * a ^ i.val := by rw [hzb]
            _ = b * (z * a ^ i.val) := by rw [mul_assoc]
            _ = b * (a ^ i.val * z) := by rw [hza_pow]
            _ = (b * a ^ i.val) * z := by rw [mul_assoc]
      -- Build the combined map fourP_V p → G: (j, d) ↦ z^j.val * f_dih(d)
      let f_fn : fourP_V p → G := fun ⟨j, d⟩ => z ^ (Multiplicative.toAdd j).val * f_dih d
      have hz_comm_f_dih : ∀ (k : ℕ) (d : DihedralGroup p),
          z ^ k * f_dih d = f_dih d * z ^ k := by
        intro k d; induction k with
        | zero => simp
        | succ n ih =>
          calc z ^ (n + 1) * f_dih d = z ^ n * z * f_dih d := by rw [pow_succ]
            _ = z ^ n * (z * f_dih d) := by rw [mul_assoc]
            _ = z ^ n * (f_dih d * z) := by rw [hz_comm_dih]
            _ = z ^ n * f_dih d * z := by rw [mul_assoc]
            _ = f_dih d * z ^ n * z := by rw [ih]
            _ = f_dih d * (z ^ n * z) := by rw [mul_assoc]
            _ = f_dih d * z ^ (n + 1) := by rw [← pow_succ]
      have hf_mul : ∀ x y, f_fn (x * y) = f_fn x * f_fn y := by
        intro ⟨j₁, d₁⟩ ⟨j₂, d₂⟩
        change z ^ (Multiplicative.toAdd (j₁ * j₂)).val * f_dih (d₁ * d₂) =
          (z ^ (Multiplicative.toAdd j₁).val * f_dih d₁) *
          (z ^ (Multiplicative.toAdd j₂).val * f_dih d₂)
        rw [f_dih.map_mul d₁ d₂]
        have hz_pow_eq : z ^ (Multiplicative.toAdd (j₁ * j₂)).val =
            z ^ ((Multiplicative.toAdd j₁).val + (Multiplicative.toAdd j₂).val) := by
          apply pow_eq_pow_iff_modEq.mpr
          have hz_ord : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz_sq
          apply Nat.ModEq.of_dvd hz_ord
          rw [toAdd_mul, ZMod.val_add]; exact Nat.mod_modEq _ _
        rw [hz_pow_eq, pow_add]
        calc z ^ (Multiplicative.toAdd j₁).val * z ^ (Multiplicative.toAdd j₂).val *
            (f_dih d₁ * f_dih d₂)
          = z ^ (Multiplicative.toAdd j₁).val *
            (z ^ (Multiplicative.toAdd j₂).val * (f_dih d₁ * f_dih d₂)) := by
              rw [mul_assoc]
          _ = z ^ (Multiplicative.toAdd j₁).val *
            (z ^ (Multiplicative.toAdd j₂).val * f_dih d₁ * f_dih d₂) := by
              rw [mul_assoc]
          _ = z ^ (Multiplicative.toAdd j₁).val *
            (f_dih d₁ * z ^ (Multiplicative.toAdd j₂).val * f_dih d₂) := by
              rw [hz_comm_f_dih _ d₁]
          _ = z ^ (Multiplicative.toAdd j₁).val *
            (f_dih d₁ * (z ^ (Multiplicative.toAdd j₂).val * f_dih d₂)) := by
              rw [mul_assoc]
          _ = (z ^ (Multiplicative.toAdd j₁).val * f_dih d₁) *
            (z ^ (Multiplicative.toAdd j₂).val * f_dih d₂) := by
              rw [← mul_assoc]
      let f : fourP_V p →* G := MonoidHom.mk' f_fn hf_mul
      haveI : Fintype G := Fintype.ofFinite G
      -- Key semidirect product facts (computed once, avoiding simp timeouts)
      have ez_eq : e z = SemidirectProduct.inr h_triv := by
        simp only [hz_def, MulEquiv.apply_symm_apply]
      have ea_eq : e a = SemidirectProduct.inl n₀ := by
        simp only [ha_def, MulEquiv.apply_symm_apply]
      have eb_eq : e b = SemidirectProduct.inr h_inv := by
        simp only [hb_def, MulEquiv.apply_symm_apply]
      have hinj : Function.Injective f := by
        rw [injective_iff_map_eq_one]
        intro ⟨j, d⟩ hx
        change z ^ (Multiplicative.toAdd j).val * f_dih d = 1 at hx
        have hx' : e (z ^ (Multiplicative.toAdd j).val * f_dih d) = 1 := by
          rw [hx, map_one]
        rw [map_mul] at hx'
        -- Extract the right component
        have hright := congrArg SemidirectProduct.right hx'
        rw [SemidirectProduct.one_right] at hright
        -- e(z^k).right = h_triv^k
        have hezr : (e (z ^ (Multiplicative.toAdd j).val)).right =
            h_triv ^ (Multiplicative.toAdd j).val := by
          rw [map_pow, ez_eq, ← map_pow, SemidirectProduct.right_inr]
        rw [SemidirectProduct.mul_right] at hright
        rw [hezr] at hright
        rcases d with (i | i)
        · -- d = r i: e(a^i.val).right = 1
          have hefr : (e (f_dih (DihedralGroup.r i))).right = 1 := by
            change (e (a ^ i.val)).right = 1
            rw [map_pow, ea_eq, ← map_pow, SemidirectProduct.right_inl]
          rw [hefr, mul_one] at hright
          have hjv : (Multiplicative.toAdd j).val = 0 := by
            by_contra hjv_ne
            have hjv_lt : (Multiplicative.toAdd j).val < 2 := ZMod.val_lt _
            have hjv1 : (Multiplicative.toAdd j).val = 1 := by omega
            rw [hjv1, pow_one] at hright
            exact h_triv_ne_1 hright
          rw [hjv] at hx; simp only [pow_zero, one_mul] at hx
          change a ^ i.val = 1 at hx
          have hi0 : i = 0 := by
            rw [← ZMod.val_eq_zero]
            have h_dvd : orderOf a ∣ i.val := orderOf_dvd_of_pow_eq_one hx
            rw [ha_ord] at h_dvd
            exact Nat.eq_zero_of_dvd_of_lt h_dvd (ZMod.val_lt i)
          ext
          · change j = 1
            have hj_zero : Multiplicative.toAdd j = (0 : ZMod 2) := by
              rwa [← ZMod.val_eq_zero]
            change j = Multiplicative.ofAdd 0
            rw [← hj_zero, ofAdd_toAdd]
          · rw [hi0]; exact DihedralGroup.one_def.symm
        · -- d = sr i: e(b * a^i.val).right = h_inv
          have hefr : (e (f_dih (DihedralGroup.sr i))).right = h_inv := by
            change (e (b * a ^ i.val)).right = h_inv
            rw [map_mul, map_pow, eb_eq, ea_eq, ← map_pow,
              SemidirectProduct.mul_right, SemidirectProduct.right_inr,
              SemidirectProduct.right_inl, mul_one]
          rw [hefr] at hright
          exfalso
          have h_inv_eq : h_inv = (h_triv ^ (Multiplicative.toAdd j).val)⁻¹ := by
            have := mul_left_cancel (a := h_triv ^ (Multiplicative.toAdd j).val)
              (b := h_inv) (c := (h_triv ^ (Multiplicative.toAdd j).val)⁻¹)
              (by rw [hright, mul_inv_cancel])
            exact this
          have hφ_hinv_1 : φ h_inv = 1 := by
            rw [h_inv_eq, map_inv, map_pow, hφ_triv]; simp
          have h1 : n₀ = n₀⁻¹ := by
            have := hφ_inv n₀; rw [hφ_hinv_1] at this; simpa using this
          have h_n₀_sq : n₀ ^ 2 = 1 := by
            rw [sq]; conv_lhs => lhs; rw [h1]
            exact inv_mul_cancel n₀
          have h_ord_dvd : orderOf n₀ ∣ 2 := orderOf_dvd_of_pow_eq_one h_n₀_sq
          rw [hn₀_ord] at h_ord_dvd
          exact absurd (Nat.le_of_dvd (by norm_num) h_ord_dvd) (by omega)
      -- f bijective by cardinality
      have hbij : Function.Bijective f :=
        (Fintype.bijective_iff_injective_and_card f).mpr
          ⟨hinj, by
            rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
              card_fourP_V, hG]⟩
      right; right; right
      exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

/-- When `p ≡ 3 [MOD 4]` and `p ≥ 5`, every group of order `4p` falls into one of 4 classes. -/
theorem fourP_classification_mod3 {p : ℕ} (hp : p.Prime) (hpge : 5 ≤ p)
    (hmod : p % 4 = 3) {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 4 * p) :
    Nonempty (G ≃* fourP_I p) ∨
    Nonempty (G ≃* fourP_II p) ∨
    Nonempty (G ≃* fourP_III p) ∨
    Nonempty (G ≃* fourP_V p) := by
  have hp_ne_zero : 4 * p ≠ 0 := by
    have := hp.pos; positivity
  have hp2 : p ≠ 2 := by omega
  by_cases hcyc : IsCyclic G
  · haveI := hcyc
    have hI : Nonempty (G ≃* CyclicRep (4 * p)) := cyclicRep_classification hp_ne_zero hG
    left
    simpa [fourP_I, CyclicRep] using hI
  · obtain ⟨N, H, φ, _, hcardN, hcardH, ⟨e⟩⟩ := fourP_semidirectProduct hp hpge hG
    exact fourP_classification_mod3_aux hp hp2 hmod hG hcyc N H φ hcardN hcardH e


/-- `IsClassif` packaging for `p ≡ 3 [MOD 4]`, `p ≥ 5`. -/
theorem fourP_isClassif_mod3 {p : ℕ} (hp : p.Prime) (hpge : 5 ≤ p) (hmod : p % 4 = 3) :
    IsClassif (4 * p) (rep4 (fourP_I p) (fourP_II p) (fourP_III p) (fourP_V p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp1 : 2 < p := by
    have := hp.two_le; omega
  let hcomplete3 : ∀ (G : Type) [Group G], Nat.card G = 4 * p → Nonempty (G ≃* fourP_I p) ∨
      Nonempty (G ≃* fourP_II p) ∨ Nonempty (G ≃* fourP_III p) ∨ Nonempty (G ≃* fourP_V p) := by
    intro G _ hG
    haveI : Finite G := Nat.finite_of_card_ne_zero (by
      rw [hG]; exact mul_ne_zero (by norm_num) hp.pos.ne')
    exact fourP_classification_mod3 hp hpge hmod hG
  exact isClassif_four (fourP_I p) (fourP_II p) (fourP_III p) (fourP_V p)
    (card_fourP_I (p := p)) (card_fourP_II (p := p))
    (card_fourP_III (p := p) hp2) (card_fourP_V (p := p))
    hcomplete3
    (fourP_I_ne_II (p := p) hp2) (fourP_I_ne_III (p := p) hp2)
    (fourP_I_ne_V (p := p) hp1)
    (fourP_II_ne_III (p := p) hp2) (fourP_II_ne_V (p := p) hp1)
    (fourP_III_ne_V (p := p) hp2)

/-! ### Exhaustiveness (5 classes, p ≡ 1 mod 4) -/

/-- When `p ≡ 1 [MOD 4]`, if a unit `u` satisfies `u ^ 4 = 1` in `(ZMod p)ˣ`,
then `u = 1` or `u = -1` or `u ^ 2 = -1`. -/
private theorem units_pow_four_eq_one_iff_mod1 {p : ℕ} [Fact p.Prime] (_ : p % 4 = 1)
    (u : (ZMod p)ˣ) (hu : u ^ 4 = 1) : u = 1 ∨ u = -1 ∨ u ^ 2 = -1 := by
  have hp_prime := Fact.out (p := p.Prime)
  haveI : NeZero p := NeZero.of_pos hp_prime.pos
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  · by_cases hun1 : u = -1
    · exact Or.inr (Or.inl hun1)
    · exact Or.inr (Or.inr (sq_eq_neg_one_of_pow_four (p := p) u hu hu1 hun1))

/-- When `p ≡ 1 [MOD 4]`, every group of order `4p` falls into one of 5 classes. -/
theorem fourP_classification_mod1 {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (c : (ZMod p)ˣ) (hcsq : c ^ 2 = -1)
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 4 * p) :
    Nonempty (G ≃* fourP_I p) ∨
    Nonempty (G ≃* fourP_II p) ∨
    Nonempty (G ≃* fourP_III p) ∨
    Nonempty (G ≃* fourP_IV p c (by rw [show (4 : ℕ) = 2 * 2 from by ring,
      pow_mul, hcsq, neg_one_sq])) ∨
    Nonempty (G ≃* fourP_V p) := by
  -- For p ≡ 1 mod 4, the unit group (Z/p)ˣ is cyclic of order p-1 which is divisible by 4,
  -- so there exist elements c with c² = -1. This enables the additional Type IV.
  -- The classification follows the same pattern as mod3, with the extra Type IV
  -- when the Sylow-2 is cyclic and the action is via c (where c² = -1).
  have hp_ne_zero : 4 * p ≠ 0 := by
    have := hp.pos; positivity
  haveI : Fact p.Prime := ⟨hp⟩
  have hpge : 5 ≤ p := by
    have h3 : p ≠ 3 := by
      intro h; rw [h] at hmod; norm_num at hmod
    have h2 : p ≠ 2 := by
      intro h; rw [h] at hmod; norm_num at hmod
    have := hp.two_le
    omega
  have hp2 : p ≠ 2 := by omega
  by_cases hcyc : IsCyclic G
  · haveI := hcyc
    have hI : Nonempty (G ≃* CyclicRep (4 * p)) := cyclicRep_classification hp_ne_zero hG
    left
    simpa [fourP_I, CyclicRep] using hI
  · -- Not cyclic. Decompose as semidirect product G ≃* N ⋊[φ] H where |N|=p, |H|=4
    obtain ⟨N, H, φ, hnorm, hcardN, hcardH, ⟨e⟩⟩ := fourP_semidirectProduct hp hpge hG
    have hiN : Nonempty (N ≃* Multiplicative (ZMod p)) := prime_classification hp hcardN
    have hp_cop_2 : Nat.Coprime 2 p :=
      Nat.prime_two.coprime_iff_not_dvd.mpr fun h =>
        have := hp.eq_one_or_self_of_dvd 2 h
        this.elim (fun h1 => by omega) (fun h2 => hp2 h2.symm)
    have hp_cop_4 : Nat.Coprime 4 p := by
      have htemp := (Nat.coprime_pow_right_iff (by norm_num : 0 < 2) p 2).mpr hp_cop_2.symm
      simpa [show (2 : ℕ) ^ 2 = 4 by norm_num] using htemp.symm
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    have hcardH_sq : Nat.card H = 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hcardH]
    rcases prime_sq_classification (p := 2) hcardH_sq with (hHcyc | hHk4)
    · -- H ≅ C₄
      obtain ⟨iH_cyc⟩ := hHcyc
      have iH : H ≃* Multiplicative (ZMod 4) := by simpa [CyclicRep] using iH_cyc
      obtain ⟨iN⟩ := hiN
      have hN_cyc : IsCyclic N := isCyclic_of_card_eq_prime hp hcardN
      have hh₀_ord : orderOf (iH.symm (Multiplicative.ofAdd (1 : ZMod 4))) = 4 := by
        rw [MulEquiv.orderOf_eq iH.symm, orderOf_ofAdd_eq_addOrderOf,
          ZMod.addOrderOf_one 4]
      have hn₀_ord : orderOf (iN.symm (Multiplicative.ofAdd (1 : ZMod p))) = p := by
        haveI : NeZero p := ⟨hp.ne_zero⟩
        rw [MulEquiv.orderOf_eq iN.symm, orderOf_ofAdd_eq_addOrderOf,
          ZMod.addOrderOf_one p]
      set h₀ := iH.symm (Multiplicative.ofAdd (1 : ZMod 4)) with hh₀_def
      set n₀ := iN.symm (Multiplicative.ofAdd (1 : ZMod p)) with hn₀_def
      by_cases hcomm : ∀ a b : G, a * b = b * a
      · -- Abelian C₄: φ trivial → G ≅ N×H ≅ Z/p×C₄ ≅ Z/(4p) → cyclic, contradiction with hcyc
        haveI : CommGroup G := { mul_comm := hcomm }
        have h_sd_comm : ∀ a b : SemidirectProduct N H φ, a * b = b * a := by
          intro a b
          have h_eq := hcomm (e.symm a) (e.symm b)
          apply_fun e at h_eq
          simpa [map_mul e, MulEquiv.apply_symm_apply] using h_eq
        have hφ : φ = 1 := action_trivial_of_abelian φ h_sd_comm
        subst hφ
        have hH_cyc : IsCyclic H :=
          iH.isCyclic.mpr inferInstance
        have h_cop : (Nat.card N).Coprime (Nat.card H) := by
          rw [hcardN, hcardH]
          have htemp := (Nat.coprime_pow_right_iff (by norm_num : 0 < 2) p 2).mpr hp_cop_2.symm
          simpa [show (2 : ℕ) ^ 2 = 4 by norm_num] using htemp
        have h_prod_cyc : IsCyclic (N × H) :=
          (Group.isCyclic_prod_iff.2 ⟨hN_cyc, hH_cyc, h_cop⟩)
        have hG_cyc : IsCyclic G :=
          isCyclic_of_surjective ((e.trans SemidirectProduct.mulEquivProd).symm.toMonoidHom)
            (MulEquiv.surjective _)
        exact absurd hG_cyc hcyc
      · -- Non-abelian C₄
        have hh₀4 : h₀ ^ 4 = 1 := by
          rw [← hh₀_ord]; exact pow_orderOf_eq_one h₀
        have hφh₀4 : (φ h₀) ^ 4 = 1 := by
          rw [← map_pow, hh₀4, map_one]
        -- Conjugate φ h₀ by iN to get an automorphism of Multiplicative (ZMod p)
        let ψ : MulAut (Multiplicative (ZMod p)) :=
          (iN.symm.trans (φ h₀)).trans iN
        let conj_iN : MulAut N →* MulAut (Multiplicative (ZMod p)) :=
          { toFun := fun σ => (iN.symm.trans σ).trans iN
            map_one' := by ext x; simp
            map_mul' := fun σ τ => by ext x; simp }
        have hψ_eq : ψ = conj_iN (φ h₀) := rfl
        have h_ord_ψ : orderOf ψ ∣ 4 := by
          rw [hψ_eq]
          apply orderOf_dvd_of_pow_eq_one
          rw [← map_pow, hφh₀4, map_one]
        obtain ⟨u, hu⟩ := mulEquiv_eq_unitAutHom (p := p) ψ
        have hu4 : u ^ 4 = 1 := by
          have hinj : Function.Injective (unitAutHom (p := p)) := by
            intro u v h
            have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod p)) =
                     unitAutHom v (Multiplicative.ofAdd (1 : ZMod p)) := by rw [h]
            simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
            apply Units.ext
            exact congrArg Multiplicative.toAdd h1
          have h_ord_u : orderOf u ∣ 4 := by
            have h_eq : orderOf (unitAutHom u) = orderOf u :=
              orderOf_injective (unitAutHom (p := p)) hinj u
            rw [← h_eq, ← hu]
            exact h_ord_ψ
          apply (orderOf_dvd_iff_pow_eq_one (x := u) (n := 4)).mp
          exact h_ord_u
        have hu_cases := units_pow_four_eq_one_iff_mod1 hmod u hu4
        rcases hu_cases with (hu1 | hun1 | husq_neg)
        · -- u = 1
          have hψ1 : ψ = 1 := by rw [hu, hu1, map_one]
          have hφh₀1 : φ h₀ = 1 := by
            apply MulEquiv.ext; intro n
            apply iN.injective
            have hψ1_eq : ∀ x, ψ x = x := by rw [hψ1]; simp
            have htemp := hψ1_eq (iN n)
            dsimp [ψ] at htemp
            simpa using htemp
          -- h₀ generates H since orderOf h₀ = 4 = card H
          have hgen : ∀ h : H, h ∈ Subgroup.zpowers h₀ := by
            have hcz : Nat.card (Subgroup.zpowers h₀ : Subgroup H) = Nat.card H := by
              rw [Nat.card_zpowers, hh₀_ord, hcardH]
            have hz_eq : Subgroup.zpowers h₀ = ⊤ :=
              Subgroup.eq_top_of_card_eq _ hcz
            intro h; rw [hz_eq]; trivial
          have hφ1 : φ = 1 := by
            ext h n
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen h)
            have hφh_eq_one : φ h = 1 := by
              calc
                φ h = φ (h₀ ^ k) := by rw [hk]
                _ = (φ h₀) ^ k := by rw [map_zpow]
                _ = 1 ^ k := by rw [hφh₀1]
                _ = 1 := by simp
            simp [hφh_eq_one]
          -- φ = 1 implies SemidirectProduct is direct product, which is abelian
          have h_sd_comm : ∀ a b : SemidirectProduct N H φ, a * b = b * a := by
            rw [hφ1]
            intro a b
            apply (SemidirectProduct.mulEquivProd).injective
            have hN_comm : ∀ n1 n2 : N, n1 * n2 = n2 * n1 := by
              intro n1 n2; apply iN.injective; simp [mul_comm]
            have hH_comm : ∀ h1 h2 : H, h1 * h2 = h2 * h1 := by
              intro h1 h2; apply iH.injective; simp [mul_comm]
            simp only [map_mul, SemidirectProduct.mulEquivProd_apply]
            simp [hN_comm a.left b.left, hH_comm a.right b.right]
          have hG_comm : ∀ a b : G, a * b = b * a := by
            intro a b
            have h_eq := h_sd_comm (e a) (e b)
            apply_fun e.symm at h_eq
            simpa using h_eq
          exact absurd hG_comm hcomm
        · -- u = -1
          have hψ_eq : ψ = unitAutHom (-1) := by rw [hu, hun1]
          have hφh₀_inv : ∀ n : N, φ h₀ n = n⁻¹ := by
            intro n
            apply iN.injective
            calc
              iN (φ h₀ n) = ψ (iN n) := by dsimp [ψ]; simp
              _ = unitAutHom (-1) (iN n) := by rw [hψ_eq]
              _ = (iN n)⁻¹ := by
                let m := Multiplicative.toAdd (iN n)
                have hm : iN n = Multiplicative.ofAdd m :=
                  (ofAdd_toAdd _).symm
                rw [hm]
                simp [unitAutHom_apply]
              _ = iN (n⁻¹) := by simp
          -- Now construct a, b in G and apply nonempty_mulEquiv_nonabRep
          set a := e.symm (SemidirectProduct.inl n₀) with ha_def
          set b := e.symm (SemidirectProduct.inr h₀) with hb_def
          have ha : orderOf a = p := by
            rw [ha_def, MulEquiv.orderOf_eq e.symm,
              orderOf_injective (SemidirectProduct.inl : N →* SemidirectProduct N H φ)
                SemidirectProduct.inl_injective n₀, hn₀_ord]
          have hb : orderOf b = 4 := by
            rw [hb_def, MulEquiv.orderOf_eq e.symm,
              orderOf_injective (SemidirectProduct.inr : H →* SemidirectProduct N H φ)
                SemidirectProduct.inr_injective h₀, hh₀_ord]
          have ha_pow_p : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
          have ha_inv_eq_pow_sub : a⁻¹ = a ^ (p - 1) := by
            apply (eq_inv_of_mul_eq_one_left ?_).symm
            calc
              a ^ (p - 1) * a = a ^ ((p - 1) + 1) := by rw [pow_succ]
              _ = a ^ p := by rw [Nat.sub_add_cancel (by omega : 1 ≤ p)]
              _ = 1 := ha_pow_p
          have h_val_neg_one : ((-1 : (ZMod p)ˣ).val : ZMod p).val = p - 1 := by
            have hp_eq : ((p - 1 : ℕ).succ : ℕ) = p := by omega
            have htemp : ((-1 : (ZMod p)ˣ).val : ZMod p) = (-1 : ZMod p) := by simp
            rw [htemp]
            have h := ZMod.val_neg_one (p - 1)
            rw [hp_eq] at h
            simpa using h
          have hconj : b * a * b⁻¹ = a ^ (((-1 : (ZMod p)ˣ).val : ZMod p).val) := by
            calc
              b * a * b⁻¹ = e.symm (SemidirectProduct.inr h₀ * SemidirectProduct.inl n₀ *
                (SemidirectProduct.inr h₀)⁻¹) := by simp [ha_def, hb_def]
              _ = e.symm (SemidirectProduct.inl (φ h₀ n₀)) := by
                simp [SemidirectProduct.inl_aut]
              _ = e.symm (SemidirectProduct.inl (n₀⁻¹)) := by rw [hφh₀_inv n₀]
              _ = e.symm ((SemidirectProduct.inl n₀)⁻¹) := by simp
              _ = a⁻¹ := by simp [ha_def]
              _ = a ^ (p - 1) := by rw [ha_inv_eq_pow_sub]
              _ = a ^ (((-1 : (ZMod p)ˣ).val : ZMod p).val) := by rw [h_val_neg_one]
          have hcop : Nat.Coprime p 4 := hp_cop_4.symm
          have hcardG : Nat.card G = p * 4 := by
            rw [hG]; ring
          haveI : NeZero p := ⟨hp.ne_zero⟩
          haveI : NeZero 4 := ⟨by norm_num⟩
          have h_nonab : Nonempty (G ≃* NonabRep (-1 : (ZMod p)ˣ) (neg_one_pow_four_units p)) :=
            nonempty_mulEquiv_nonabRep a b ha hb (-1 : (ZMod p)ˣ) (neg_one_pow_four_units p)
              hconj hcop hcardG
          right; right; left
          simpa [fourP_III] using h_nonab
        · -- u ^ 2 = -1
          -- Derive conjugation relation: b * a * b⁻¹ = a ^ (u : ZMod p).val
          have hψ_eq : ψ = unitAutHom u := hu
          have hφh₀_act : ∀ n : N, iN (φ h₀ n) = unitAutHom u (iN n) := by
            intro n
            calc
              iN (φ h₀ n) = ψ (iN n) := by dsimp [ψ]; simp
              _ = unitAutHom u (iN n) := by rw [hψ_eq]
          set a := e.symm (SemidirectProduct.inl n₀) with ha_def
          set b := e.symm (SemidirectProduct.inr h₀) with hb_def
          have ha : orderOf a = p := by
            rw [ha_def, MulEquiv.orderOf_eq e.symm,
              orderOf_injective (SemidirectProduct.inl : N →* SemidirectProduct N H φ)
                SemidirectProduct.inl_injective n₀, hn₀_ord]
          have hb : orderOf b = 4 := by
            rw [hb_def, MulEquiv.orderOf_eq e.symm,
              orderOf_injective (SemidirectProduct.inr : H →* SemidirectProduct N H φ)
                SemidirectProduct.inr_injective h₀, hh₀_ord]
          have hconj_u : b * a * b⁻¹ = a ^ (u : ZMod p).val := by
            have hn₀_pow : n₀ ^ (u : ZMod p).val = φ h₀ n₀ := by
              apply iN.injective
              calc
                iN (n₀ ^ (u : ZMod p).val) = (iN n₀) ^ (u : ZMod p).val := by simp
                _ = (Multiplicative.ofAdd (1 : ZMod p)) ^ (u : ZMod p).val := by
                  simp [hn₀_def]
                _ = Multiplicative.ofAdd ((u : ZMod p).val • (1 : ZMod p)) := by
                  simpa using (ofAdd_nsmul (n := (u : ZMod p).val)
                    (a := (1 : ZMod p))).symm
                _ = Multiplicative.ofAdd (u : ZMod p) := by simp
                _ = unitAutHom u (Multiplicative.ofAdd (1 : ZMod p)) := by
                  simp [unitAutHom_apply]
                _ = unitAutHom u (iN n₀) := by simp [hn₀_def]
                _ = iN (φ h₀ n₀) := by rw [← hφh₀_act n₀]
            calc
              b * a * b⁻¹ = e.symm (SemidirectProduct.inr h₀ * SemidirectProduct.inl n₀ *
                (SemidirectProduct.inr h₀)⁻¹) := by simp [ha_def, hb_def]
              _ = e.symm (SemidirectProduct.inl (φ h₀ n₀)) := by
                simp [SemidirectProduct.inl_aut]
              _ = e.symm (SemidirectProduct.inl (n₀ ^ (u : ZMod p).val)) := by rw [hn₀_pow]
              _ = e.symm ((SemidirectProduct.inl n₀) ^ (u : ZMod p).val) := by simp
              _ = a ^ (u : ZMod p).val := by simp [ha_def]
          have hcop : Nat.Coprime p 4 := hp_cop_4.symm
          have hcardG : Nat.card G = p * 4 := by
            rw [hG]; ring
          haveI : NeZero p := ⟨hp.ne_zero⟩
          haveI : NeZero 4 := ⟨by norm_num⟩
          have hc4 : c ^ 4 = 1 := by
            rw [show (4 : ℕ) = 2 * 2 from by ring, pow_mul, hcsq, neg_one_sq]
          by_cases hcu : c = u
          · -- c = u
            have h_nonab : Nonempty (G ≃* NonabRep u hu4) :=
              nonempty_mulEquiv_nonabRep a b ha hb u hu4 hconj_u hcop hcardG
            right; right; right; left
            subst hcu
            simpa [fourP_IV] using h_nonab
          · -- c ≠ u, so c = u^3 (both have order 4 and c^2 = u^2 = -1)
            have hcu3 : c = u ^ 3 := by
              have h_prod_sq : (c⁻¹ * u) ^ 2 = 1 := by
                calc
                  (c⁻¹ * u) ^ 2 = (c⁻¹ * u) * (c⁻¹ * u) := by rw [sq]
                  _ = c⁻¹ * u * (c⁻¹ * u) := rfl
                  _ = c⁻¹ * (u * c⁻¹) * u := by group
                  _ = c⁻¹ * (c⁻¹ * u) * u := by rw [mul_comm u c⁻¹]
                  _ = (c⁻¹ * c⁻¹) * (u * u) := by group
                  _ = (c ^ 2)⁻¹ * (u ^ 2) := by simp [sq]
                  _ = (-1)⁻¹ * (-1) := by rw [hcsq, husq_neg]
                  _ = 1 := by simp
              have h_cases := units_sq_eq_one_of_prime (c⁻¹ * u) h_prod_sq
              rcases h_cases with (h1 | h1)
              · -- c⁻¹ * u = 1 → c = u, contradiction
                exfalso
                have hcu_eq : c = u := by
                  calc
                    c = c * 1 := by simp
                    _ = c * (c⁻¹ * u) := by rw [← h1]
                    _ = (c * c⁻¹) * u := by group
                    _ = 1 * u := by simp
                    _ = u := by simp
                exact hcu hcu_eq
              · -- c⁻¹ * u = -1 → u = -c → c = -u = u² * u = u³
                have htemp : u = -c := by
                  calc
                    u = c * (c⁻¹ * u) := by group
                    _ = c * (-1) := by rw [h1]
                    _ = -c := by simp
                calc
                  c = -(-c) := by simp
                  _ = -u := by rw [← htemp]
                  _ = (-1) * u := by simp
                  _ = u ^ 2 * u := by rw [← husq_neg]
                  _ = u ^ 3 := by simp [pow_succ]
            have hb3_ord : orderOf (b ^ 3) = 4 := by
              rw [orderOf_pow' b (by norm_num : 3 ≠ 0), hb]
              have hgcd : Nat.gcd 4 3 = 1 := by decide
              rw [hgcd, Nat.div_one]
            have hconj_b3 : b ^ 3 * a * (b ^ 3)⁻¹ = a ^ (c : ZMod p).val := by
              have hconj_bk : ∀ (k : ℕ), b ^ k * a * (b ^ k)⁻¹ =
                  a ^ (((u ^ k : (ZMod p)ˣ) : ZMod p)).val := by
                intro k
                induction k with
                | zero => simp [ZMod.val_one]
                | succ n ih =>
                  have hsplit : b ^ (n + 1) * a * (b ^ (n + 1))⁻¹
                      = b * (b ^ n * a * (b ^ n)⁻¹) * b⁻¹ := by
                    rw [pow_succ, mul_inv_rev]; group
                  rw [hsplit, ih, ← conj_pow, hconj_u, ← pow_mul]
                  apply pow_eq_pow_iff_modEq.mpr
                  rw [ha, show (((u ^ (n + 1) : (ZMod p)ˣ) : ZMod p)).val
                        = ((u : ZMod p).val * (((u ^ n : (ZMod p)ˣ) : ZMod p)).val) % p from by
                      rw [pow_succ', Units.val_mul, ZMod.val_mul]]
                  exact (Nat.mod_modEq _ _).symm
              rw [hconj_bk 3, hcu3]
            have h_nonab : Nonempty (G ≃* NonabRep c hc4) :=
              nonempty_mulEquiv_nonabRep a (b ^ 3) ha hb3_ord c hc4 hconj_b3 hcop hcardG
            right; right; right; left
            simpa [fourP_IV] using h_nonab
    · -- H ≅ K₄
      by_cases hcomm : ∀ a b : G, a * b = b * a
      · -- Abelian K₄ → Type II: G ≅ Z/2 × Z/(2p) = fourP_II p
        haveI : CommGroup G := { mul_comm := hcomm }
        have h_sd_comm : ∀ a b : SemidirectProduct N H φ, a * b = b * a := by
          intro a b
          have h_eq := hcomm (e.symm a) (e.symm b)
          apply_fun e at h_eq
          simpa [map_mul e, MulEquiv.apply_symm_apply] using h_eq
        have hφ : φ = 1 := action_trivial_of_abelian φ h_sd_comm
        subst hφ
        -- G ≃* N × H via SemidirectProduct.mulEquivProd
        have hG_NH : Nonempty (G ≃* (N × H)) :=
          ⟨e.trans SemidirectProduct.mulEquivProd⟩
        obtain ⟨eG_NH⟩ := hG_NH
        -- N ≅ Z/p, H ≅ Z/2 × Z/2
        obtain ⟨iN⟩ := hiN
        obtain ⟨iH⟩ := hHk4
        let iH' : H ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
          simpa [ElemAbelianRep, CyclicRep] using iH
        right; left
        let A := Multiplicative (ZMod p)
        let B := Multiplicative (ZMod 2)
        let C := Multiplicative (ZMod 2)
        let D := Multiplicative (ZMod (2 * p))
        have h_crt : C × A ≃* D := crtProd 2 p hp_cop_2
        have h_prod_iso : (N × H) ≃* (B × D) :=
          let e1 := MulEquiv.prodCongr iN iH'
          let e2 := (MulEquiv.prodAssoc (M := A) (N := B) (P := C)).symm
          let e3 := MulEquiv.prodCongr (MulEquiv.prodComm (M := A) (N := B))
            (MulEquiv.refl (M := C))
          let e4 := MulEquiv.prodAssoc (M := B) (N := A) (P := C)
          let e5 := MulEquiv.prodCongr (MulEquiv.refl (M := B))
            (MulEquiv.prodComm (M := A) (N := C))
          let e6 := MulEquiv.prodCongr (MulEquiv.refl (M := B)) h_crt
          (e1.trans e2).trans e3 |>.trans e4 |>.trans e5 |>.trans e6
        refine ⟨eG_NH.trans h_prod_iso⟩
      · -- Non-abelian K₄ → Type V: G ≅ ℤ/2 × D_{2p}
        obtain ⟨iN⟩ := hiN
        obtain ⟨iH⟩ := hHk4
        let iH' : H ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
          simpa [ElemAbelianRep, CyclicRep] using iH
        -- generators of H
        set u₁ := iH'.symm (Multiplicative.ofAdd 1, 1) with hu₁_def
        set u₂ := iH'.symm (1, Multiplicative.ofAdd 1) with hu₂_def
        have hzmod2_add : (1 : ZMod 2) + 1 = 0 := by
          have h2 : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
          calc (1 : ZMod 2) + 1 = 2 := by ring
            _ = 0 := h2
        have hu₁_sq : u₁ ^ 2 = 1 := by
          have h : iH' u₁ = (Multiplicative.ofAdd 1, (1 : Multiplicative (ZMod 2))) :=
            MulEquiv.apply_symm_apply iH' _
          apply iH'.injective; simp only [map_pow, map_one, h]
          ext <;> simp [sq, hzmod2_add]
        have hu₂_sq : u₂ ^ 2 = 1 := by
          have h : iH' u₂ = ((1 : Multiplicative (ZMod 2)), Multiplicative.ofAdd 1) :=
            MulEquiv.apply_symm_apply iH' _
          apply iH'.injective; simp only [map_pow, map_one, h]
          ext <;> simp [sq, hzmod2_add]
        -- φ(u₁)² = 1 and φ(u₂)² = 1 in Aut(N)
        have hφu₁_sq : (φ u₁) ^ 2 = 1 := by rw [← map_pow, hu₁_sq, map_one]
        have hφu₂_sq : (φ u₂) ^ 2 = 1 := by rw [← map_pow, hu₂_sq, map_one]
        -- Conjugate to automorphisms of Multiplicative (ZMod p)
        let ψ₁ := (iN.symm.trans (φ u₁)).trans iN
        let ψ₂ := (iN.symm.trans (φ u₂)).trans iN
        have hψ₁_sq : ψ₁ ^ 2 = 1 := by
          have key : ∀ n : N, ψ₁ (ψ₁ (iN n)) = iN n := by
            intro n; dsimp only [ψ₁, MulEquiv.trans_apply]
            simp only [MulEquiv.symm_apply_apply]
            congr 1
            rw [← MulAut.mul_apply, ← sq, hφu₁_sq, MulAut.one_apply]
          ext x
          obtain ⟨n, rfl⟩ := iN.surjective x
          simp only [MulAut.one_apply, pow_succ, pow_zero, MulAut.mul_apply, key]
        have hψ₂_sq : ψ₂ ^ 2 = 1 := by
          have key : ∀ n : N, ψ₂ (ψ₂ (iN n)) = iN n := by
            intro n; dsimp only [ψ₂, MulEquiv.trans_apply]
            simp only [MulEquiv.symm_apply_apply]
            congr 1
            rw [← MulAut.mul_apply, ← sq, hφu₂_sq, MulAut.one_apply]
          ext x
          obtain ⟨n, rfl⟩ := iN.surjective x
          simp only [MulAut.one_apply, pow_succ, pow_zero, MulAut.mul_apply, key]
        -- Each ψᵢ = unitAutHom(uᵢ) for some unit uᵢ with uᵢ² = 1
        obtain ⟨v₁, hv₁⟩ := mulEquiv_eq_unitAutHom (p := p) ψ₁
        obtain ⟨v₂, hv₂⟩ := mulEquiv_eq_unitAutHom (p := p) ψ₂
        have hv₁_sq : v₁ ^ 2 = 1 := by
          have hinj : Function.Injective (unitAutHom (p := p)) := by
            intro u v h
            have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod p)) =
                     unitAutHom v (Multiplicative.ofAdd (1 : ZMod p)) := by rw [h]
            simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
            exact Units.ext (congrArg Multiplicative.toAdd h1)
          have := hinj (by rw [map_pow, ← hv₁, hψ₁_sq, map_one] :
            unitAutHom (v₁ ^ 2) = unitAutHom 1)
          exact this
        have hv₂_sq : v₂ ^ 2 = 1 := by
          have hinj : Function.Injective (unitAutHom (p := p)) := by
            intro u v h
            have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod p)) =
                     unitAutHom v (Multiplicative.ofAdd (1 : ZMod p)) := by rw [h]
            simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
            exact Units.ext (congrArg Multiplicative.toAdd h1)
          have := hinj (by rw [map_pow, ← hv₂, hψ₂_sq, map_one] :
            unitAutHom (v₂ ^ 2) = unitAutHom 1)
          exact this
        -- v₁, v₂ ∈ {1, -1} since x² = 1 in (ZMod p)ˣ iff x = ±1
        have hv₁_cases : v₁ = 1 ∨ v₁ = -1 :=
          units_sq_eq_one_of_prime v₁ hv₁_sq
        have hv₂_cases : v₂ = 1 ∨ v₂ = -1 :=
          units_sq_eq_one_of_prime v₂ hv₂_sq
        -- φ(u) acts by inversion when the corresponding unit is -1
        have unitAutHom_neg1_inv : ∀ x : Multiplicative (ZMod p),
            unitAutHom (-1 : (ZMod p)ˣ) x = x⁻¹ := by
          intro x
          let m := Multiplicative.toAdd x
          have hm : x = Multiplicative.ofAdd m := (ofAdd_toAdd _).symm
          rw [hm]; simp [unitAutHom_apply]
        have hφ_inv_of_neg1 : ∀ (u : H) (v : (ZMod p)ˣ),
            (iN.symm.trans (φ u)).trans iN = unitAutHom v → v = -1 →
            ∀ n : N, φ u n = n⁻¹ := by
          intro u v hψ hv n
          apply iN.injective
          have h := MulEquiv.ext_iff.mp hψ (iN n)
          simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
          rw [h, hv, unitAutHom_neg1_inv]; simp
        have hφ_triv_of_1 : ∀ (u : H) (v : (ZMod p)ˣ),
            (iN.symm.trans (φ u)).trans iN = unitAutHom v → v = 1 →
            φ u = 1 := by
          intro u v hψ hv
          apply MulEquiv.ext; intro n
          have h := MulEquiv.ext_iff.mp hψ (iN n)
          simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
          have h2 : iN ((φ u) n) = iN n := by
            rw [h, hv]; simp
          exact iN.injective h2
        -- Since G is non-abelian, φ ≠ 1. So at least one of v₁, v₂ is -1.
        -- Find h_inv (inverts N) and h_triv (acts trivially).
        -- If both invert: u₁u₂ acts trivially, so use h_inv = u₁, h_triv = u₁ * u₂.
        -- Product u₁ * u₂ in H maps to (ofAdd 1, ofAdd 1) in K₄.
        have hu₁u₂ : iH' (u₁ * u₂) = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) := by
          simp [hu₁_def, hu₂_def, map_mul, MulEquiv.apply_symm_apply]
        have hu₁_comm_u₂ : Commute u₁ u₂ := by
          change u₁ * u₂ = u₂ * u₁
          apply iH'.injective; simp [map_mul, mul_comm]
        have hu₁u₂_sq : (u₁ * u₂) ^ 2 = 1 := by
          rw [hu₁_comm_u₂.mul_pow, hu₁_sq, hu₂_sq, one_mul]
        have hφu₁u₂ : φ (u₁ * u₂) = φ u₁ * φ u₂ := map_mul φ u₁ u₂
        -- Obtain h_inv (inverts) and h_triv (trivial), both order 2, h_triv ≠ 1
        obtain ⟨h_inv, h_triv, hφ_inv, hφ_triv, h_inv_sq, h_triv_sq, h_triv_ne_1⟩ :
            ∃ (h_inv h_triv : H),
              (∀ n : N, φ h_inv n = n⁻¹) ∧ (φ h_triv = 1) ∧
              h_inv ^ 2 = 1 ∧ h_triv ^ 2 = 1 ∧ h_triv ≠ 1 := by
          rcases hv₁_cases with hv₁1 | hv₁neg1 <;> rcases hv₂_cases with hv₂1 | hv₂neg1
          · -- v₁ = 1, v₂ = 1: both trivial → φ = 1 → G abelian, contradiction
            exfalso; apply hcomm
            have hφu₁_1 := hφ_triv_of_1 u₁ v₁ hv₁ hv₁1
            have hφu₂_1 := hφ_triv_of_1 u₂ v₂ hv₂ hv₂1
            -- φ u = 1 for all u since u₁, u₂ generate H
            have hφ_all : ∀ h : H, φ h = 1 := by
              intro h
              have hu₁_im : iH' u₁ = (Multiplicative.ofAdd 1, 1) :=
                MulEquiv.apply_symm_apply iH' _
              have hu₂_im : iH' u₂ = (1, Multiplicative.ofAdd 1) :=
                MulEquiv.apply_symm_apply iH' _
              have hh_decomp : h = u₁ ^ (Multiplicative.toAdd (iH' h).1).val *
                  u₂ ^ (Multiplicative.toAdd (iH' h).2).val := by
                apply iH'.injective
                rw [map_mul, map_pow, map_pow, hu₁_im, hu₂_im]
                ext
                · simp
                · simp
              rw [hh_decomp, map_mul, map_pow, map_pow, hφu₁_1, hφu₂_1]; simp
            have hφ1 : φ = 1 := by
              ext h n; have := hφ_all h; simp [this]
            -- φ = 1 → semidirect product is abelian → G is abelian
            have h_sd_comm : ∀ a b : SemidirectProduct N H φ, a * b = b * a := by
              intro a b
              have hl : a.left * b.left = b.left * a.left := by
                apply iN.injective; simp [mul_comm]
              have hr : a.right * b.right = b.right * a.right := by
                apply iH'.injective; simp [mul_comm]
              apply SemidirectProduct.ext
              · simp [SemidirectProduct.mul_left, hφ_all, hl]
              · simp [SemidirectProduct.mul_right, hr]
            intro x y
            have := h_sd_comm (e x) (e y)
            apply_fun e.symm at this; simpa using this
          · -- v₁ = 1, v₂ = -1
            have hu₁_ne_1 : u₁ ≠ 1 := by
              intro h; have := congrArg iH' h; simp [hu₁_def] at this
            exact ⟨u₂, u₁, hφ_inv_of_neg1 u₂ v₂ hv₂ hv₂neg1,
              hφ_triv_of_1 u₁ v₁ hv₁ hv₁1, hu₂_sq, hu₁_sq, hu₁_ne_1⟩
          · -- v₁ = -1, v₂ = 1
            have hu₂_ne_1 : u₂ ≠ 1 := by
              intro h; have := congrArg iH' h; simp [hu₂_def] at this
            exact ⟨u₁, u₂, hφ_inv_of_neg1 u₁ v₁ hv₁ hv₁neg1,
              hφ_triv_of_1 u₂ v₂ hv₂ hv₂1, hu₁_sq, hu₂_sq, hu₂_ne_1⟩
          · -- v₁ = -1, v₂ = -1: u₁u₂ acts trivially
            have hφu₁u₂_triv : φ (u₁ * u₂) = 1 := by
              apply MulEquiv.ext; intro n
              rw [hφu₁u₂, MulAut.mul_apply,
                hφ_inv_of_neg1 u₂ v₂ hv₂ hv₂neg1 n,
                hφ_inv_of_neg1 u₁ v₁ hv₁ hv₁neg1 n⁻¹]
              simp
            have hu₁u₂_ne_1 : u₁ * u₂ ≠ 1 := by
              intro h; have := congrArg iH' h; simp [map_mul, hu₁_def, hu₂_def] at this
            exact ⟨u₁, u₁ * u₂, hφ_inv_of_neg1 u₁ v₁ hv₁ hv₁neg1,
              hφu₁u₂_triv, hu₁_sq, hu₁u₂_sq, hu₁u₂_ne_1⟩
        -- Now we have h_inv (inverts N) and h_triv (acts trivially), both order 2.
        -- Build elements in G.
        haveI : NeZero p := ⟨hp.ne_zero⟩
        set n₀ := iN.symm (Multiplicative.ofAdd (1 : ZMod p)) with hn₀_def
        have hn₀_ord : orderOf n₀ = p := by
          rw [MulEquiv.orderOf_eq iN.symm, orderOf_ofAdd_eq_addOrderOf,
            ZMod.addOrderOf_one p]
        set a := e.symm (SemidirectProduct.inl n₀) with ha_def
        set b := e.symm (SemidirectProduct.inr h_inv) with hb_def
        set z := e.symm (SemidirectProduct.inr h_triv) with hz_def
        -- orderOf a = p
        have ha_ord : orderOf a = p := by
          rw [ha_def, MulEquiv.orderOf_eq e.symm,
            orderOf_injective SemidirectProduct.inl
              SemidirectProduct.inl_injective n₀, hn₀_ord]
        -- b² = 1
        have hb_sq : b ^ 2 = 1 := by
          apply e.injective; simp only [hb_def, map_pow, map_one, MulEquiv.apply_symm_apply]
          rw [← map_pow]; simp [h_inv_sq]
        -- b ≠ 1 (since φ h_inv ≠ 1, the action is non-trivial)
        have hb_ne_1 : b ≠ 1 := by
          intro hb1
          -- φ h_inv is inversion but if b = 1, then h_inv = 1, so φ h_inv = 1
          have hinv1 : h_inv = 1 := by
            have hb1' := congrArg e hb1
            simp only [hb_def, MulEquiv.apply_symm_apply, map_one] at hb1'
            exact SemidirectProduct.inr_injective hb1'
          have hφ_hinv_1 : φ h_inv = 1 := by rw [hinv1, map_one]
          have h_n₀_sq : n₀ ^ 2 = 1 := by
            have h1 : n₀ = n₀⁻¹ := by
              have := hφ_inv n₀; rw [hφ_hinv_1] at this; simpa using this
            rw [sq]; conv_lhs => lhs; rw [h1]
            exact inv_mul_cancel n₀
          have h_ord_dvd : orderOf n₀ ∣ 2 := orderOf_dvd_of_pow_eq_one h_n₀_sq
          rw [hn₀_ord] at h_ord_dvd
          exact absurd (Nat.le_of_dvd (by norm_num) h_ord_dvd) (by omega)
        -- b * a * b⁻¹ = a⁻¹ (the dihedral relation)
        have hba_inv : b * a * b⁻¹ = a⁻¹ := by
          apply e.injective
          have heb : e b = SemidirectProduct.inr h_inv := by
            simp only [hb_def, MulEquiv.apply_symm_apply]
          have hea : e a = SemidirectProduct.inl n₀ := by
            simp only [ha_def, MulEquiv.apply_symm_apply]
          have lhs_eq : e (b * a * b⁻¹) = SemidirectProduct.inl (φ h_inv n₀) := by
            rw [map_mul, map_mul, map_inv, heb, hea]
            simp [SemidirectProduct.inl_aut]
          have rhs_eq : e (a⁻¹) = SemidirectProduct.inl (n₀⁻¹) := by
            rw [map_inv, hea, map_inv]
          rw [lhs_eq, rhs_eq, hφ_inv n₀]
        -- z² = 1
        have hz_sq : z ^ 2 = 1 := by
          apply e.injective; simp only [hz_def, map_pow, map_one, MulEquiv.apply_symm_apply]
          rw [← map_pow]; simp [h_triv_sq]
        -- z commutes with a
        have hza : z * a = a * z := by
          apply e.injective
          rw [map_mul, map_mul]
          simp only [ha_def, hz_def, MulEquiv.apply_symm_apply]
          apply SemidirectProduct.ext
          · simp [SemidirectProduct.mul_left, hφ_triv]
          · simp [SemidirectProduct.mul_right]
        -- z commutes with b (both come from H, which is abelian)
        have hzb : z * b = b * z := by
          apply e.injective
          rw [map_mul, map_mul]
          simp only [hb_def, hz_def, MulEquiv.apply_symm_apply]
          rw [← map_mul, ← map_mul]
          congr 1
          apply iH'.injective; simp [map_mul, mul_comm]
        -- Now build the isomorphism G ≃* Multiplicative (ZMod 2) × DihedralGroup p
        have ha_pow_p : a ^ p = 1 := by rw [← ha_ord]; exact pow_orderOf_eq_one a
        have hodd : Odd p := hp.odd_of_ne_two (by omega)
        -- The map DihedralGroup p → G sending r i ↦ a^i.val, sr i ↦ b * a^i.val
        -- Combined map: (j, d) ↦ z^j.val * f_dih(d)
        -- First build f_dih using the same approach as nonempty_mulEquiv_dihedral
        have hab : a * b = b * a⁻¹ := by
          have h2 : b * a = a⁻¹ * b := by rw [← hba_inv]; group
          calc a * b = a * b * a * a⁻¹ := by group
            _ = a * (a⁻¹ * b) * a⁻¹ := by rw [← h2]; group
            _ = b * a⁻¹ := by group
        have hak : ∀ k : ℕ, a ^ k * b = b * (a⁻¹) ^ k := by
          intro k; induction k with
          | zero => simp
          | succ n ih => rw [pow_succ, mul_assoc, hab, ← mul_assoc, ih, mul_assoc, ← pow_succ]
        have hbb : b * b = 1 := by rw [← pow_two]; exact hb_sq
        have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
        have hcom : ∀ m n : ℕ, (a ^ m)⁻¹ * a ^ n = a ^ n * (a ^ m)⁻¹ :=
          fun m n => ((((Commute.refl a).pow_pow n m).inv_right).eq).symm
        have hc_add : ∀ i j : ZMod p, a ^ (i + j).val = a ^ i.val * a ^ j.val := by
          intro i j; rw [← pow_add]; apply pow_eq_pow_iff_modEq.mpr
          rw [ha_ord, ZMod.val_add]; exact Nat.mod_modEq _ _
        have hc_sub : ∀ i j : ZMod p, a ^ (j - i).val = a ^ j.val * (a ^ i.val)⁻¹ := by
          intro i j; have h := hc_add (j - i) i
          rw [sub_add_cancel] at h; exact eq_mul_inv_iff_mul_eq.mpr h.symm
        have hrsr : ∀ m n : ℕ, a ^ m * (b * a ^ n) = b * (a ^ n * (a ^ m)⁻¹) := by
          intro m n; rw [← mul_assoc, hak, mul_assoc, inv_pow, hcom]
        have hsrsr : ∀ m n : ℕ, b * a ^ m * (b * a ^ n) = a ^ n * (a ^ m)⁻¹ := by
          intro m n; rw [mul_assoc, hrsr, ← mul_assoc, ← pow_two, hb_sq, one_mul]
        let f_dih_fn : DihedralGroup p → G := fun x => match x with
          | .r i => a ^ i.val
          | .sr i => b * a ^ i.val
        have hf_dih_mul : ∀ x y, f_dih_fn (x * y) = f_dih_fn x * f_dih_fn y := by
          rintro (i | i) (j | j)
          · exact hc_add i j
          · change b * a ^ (j - i).val = a ^ i.val * (b * a ^ j.val)
            rw [hc_sub, hrsr]
          · change b * a ^ (i + j).val = b * a ^ i.val * a ^ j.val
            rw [hc_add, mul_assoc]
          · change a ^ (j - i).val = b * a ^ i.val * (b * a ^ j.val)
            rw [hc_sub, hsrsr]
        let f_dih : DihedralGroup p →* G := MonoidHom.mk' f_dih_fn hf_dih_mul
        -- z commutes with everything in range of f_dih
        have hza_pow : ∀ k : ℕ, z * a ^ k = a ^ k * z := by
          intro k; induction k with
          | zero => simp
          | succ n ih =>
            calc z * a ^ (n + 1) = z * (a ^ n * a) := by rw [pow_succ]
              _ = (z * a ^ n) * a := by rw [mul_assoc]
              _ = (a ^ n * z) * a := by rw [ih]
              _ = a ^ n * (z * a) := by rw [mul_assoc]
              _ = a ^ n * (a * z) := by rw [hza]
              _ = a ^ (n + 1) * z := by rw [← mul_assoc, ← pow_succ]
        have hz_comm_dih : ∀ d : DihedralGroup p, z * f_dih d = f_dih d * z := by
          rintro (i | i)
          · exact hza_pow i.val
          · change z * (b * a ^ i.val) = (b * a ^ i.val) * z
            calc z * (b * a ^ i.val) = (z * b) * a ^ i.val := by rw [mul_assoc]
              _ = (b * z) * a ^ i.val := by rw [hzb]
              _ = b * (z * a ^ i.val) := by rw [mul_assoc]
              _ = b * (a ^ i.val * z) := by rw [hza_pow]
              _ = (b * a ^ i.val) * z := by rw [mul_assoc]
        -- Build the combined map fourP_V p → G: (j, d) ↦ z^j.val * f_dih(d)
        let f_fn : fourP_V p → G := fun ⟨j, d⟩ => z ^ (Multiplicative.toAdd j).val * f_dih d
        have hz_comm_f_dih : ∀ (k : ℕ) (d : DihedralGroup p),
            z ^ k * f_dih d = f_dih d * z ^ k := by
          intro k d; induction k with
          | zero => simp
          | succ n ih =>
            calc z ^ (n + 1) * f_dih d = z ^ n * z * f_dih d := by rw [pow_succ]
              _ = z ^ n * (z * f_dih d) := by rw [mul_assoc]
              _ = z ^ n * (f_dih d * z) := by rw [hz_comm_dih]
              _ = z ^ n * f_dih d * z := by rw [mul_assoc]
              _ = f_dih d * z ^ n * z := by rw [ih]
              _ = f_dih d * (z ^ n * z) := by rw [mul_assoc]
              _ = f_dih d * z ^ (n + 1) := by rw [← pow_succ]
        have hf_mul : ∀ x y, f_fn (x * y) = f_fn x * f_fn y := by
          intro ⟨j₁, d₁⟩ ⟨j₂, d₂⟩
          change z ^ (Multiplicative.toAdd (j₁ * j₂)).val * f_dih (d₁ * d₂) =
            (z ^ (Multiplicative.toAdd j₁).val * f_dih d₁) *
            (z ^ (Multiplicative.toAdd j₂).val * f_dih d₂)
          rw [f_dih.map_mul d₁ d₂]
          have hz_pow_eq : z ^ (Multiplicative.toAdd (j₁ * j₂)).val =
              z ^ ((Multiplicative.toAdd j₁).val + (Multiplicative.toAdd j₂).val) := by
            apply pow_eq_pow_iff_modEq.mpr
            have hz_ord : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz_sq
            apply Nat.ModEq.of_dvd hz_ord
            rw [toAdd_mul, ZMod.val_add]; exact Nat.mod_modEq _ _
          rw [hz_pow_eq, pow_add]
          calc z ^ (Multiplicative.toAdd j₁).val * z ^ (Multiplicative.toAdd j₂).val *
              (f_dih d₁ * f_dih d₂)
            = z ^ (Multiplicative.toAdd j₁).val *
              (z ^ (Multiplicative.toAdd j₂).val * (f_dih d₁ * f_dih d₂)) := by
                rw [mul_assoc]
            _ = z ^ (Multiplicative.toAdd j₁).val *
              (z ^ (Multiplicative.toAdd j₂).val * f_dih d₁ * f_dih d₂) := by
                rw [mul_assoc]
            _ = z ^ (Multiplicative.toAdd j₁).val *
              (f_dih d₁ * z ^ (Multiplicative.toAdd j₂).val * f_dih d₂) := by
                rw [hz_comm_f_dih _ d₁]
            _ = z ^ (Multiplicative.toAdd j₁).val *
              (f_dih d₁ * (z ^ (Multiplicative.toAdd j₂).val * f_dih d₂)) := by
                rw [mul_assoc]
            _ = (z ^ (Multiplicative.toAdd j₁).val * f_dih d₁) *
              (z ^ (Multiplicative.toAdd j₂).val * f_dih d₂) := by
                rw [← mul_assoc]
        let f : fourP_V p →* G := MonoidHom.mk' f_fn hf_mul
        haveI : Fintype G := Fintype.ofFinite G
        -- Key semidirect product facts (computed once, avoiding simp timeouts)
        have ez_eq : e z = SemidirectProduct.inr h_triv := by
          simp only [hz_def, MulEquiv.apply_symm_apply]
        have ea_eq : e a = SemidirectProduct.inl n₀ := by
          simp only [ha_def, MulEquiv.apply_symm_apply]
        have eb_eq : e b = SemidirectProduct.inr h_inv := by
          simp only [hb_def, MulEquiv.apply_symm_apply]
        have hinj : Function.Injective f := by
          rw [injective_iff_map_eq_one]
          intro ⟨j, d⟩ hx
          change z ^ (Multiplicative.toAdd j).val * f_dih d = 1 at hx
          have hx' : e (z ^ (Multiplicative.toAdd j).val * f_dih d) = 1 := by
            rw [hx, map_one]
          rw [map_mul] at hx'
          -- Extract the right component
          have hright := congrArg SemidirectProduct.right hx'
          rw [SemidirectProduct.one_right] at hright
          -- e(z^k).right = h_triv^k
          have hezr : (e (z ^ (Multiplicative.toAdd j).val)).right =
              h_triv ^ (Multiplicative.toAdd j).val := by
            rw [map_pow, ez_eq, ← map_pow, SemidirectProduct.right_inr]
          rw [SemidirectProduct.mul_right] at hright
          rw [hezr] at hright
          rcases d with (i | i)
          · -- d = r i: e(a^i.val).right = 1
            have hefr : (e (f_dih (DihedralGroup.r i))).right = 1 := by
              change (e (a ^ i.val)).right = 1
              rw [map_pow, ea_eq, ← map_pow, SemidirectProduct.right_inl]
            rw [hefr, mul_one] at hright
            have hjv : (Multiplicative.toAdd j).val = 0 := by
              by_contra hjv_ne
              have hjv_lt : (Multiplicative.toAdd j).val < 2 := ZMod.val_lt _
              have hjv1 : (Multiplicative.toAdd j).val = 1 := by omega
              rw [hjv1, pow_one] at hright
              exact h_triv_ne_1 hright
            rw [hjv] at hx; simp only [pow_zero, one_mul] at hx
            change a ^ i.val = 1 at hx
            have hi0 : i = 0 := by
              rw [← ZMod.val_eq_zero]
              have h_dvd : orderOf a ∣ i.val := orderOf_dvd_of_pow_eq_one hx
              rw [ha_ord] at h_dvd
              exact Nat.eq_zero_of_dvd_of_lt h_dvd (ZMod.val_lt i)
            ext
            · change j = 1
              have hj_zero : Multiplicative.toAdd j = (0 : ZMod 2) := by
                rwa [← ZMod.val_eq_zero]
              change j = Multiplicative.ofAdd 0
              rw [← hj_zero, ofAdd_toAdd]
            · rw [hi0]; exact DihedralGroup.one_def.symm
          · -- d = sr i: e(b * a^i.val).right = h_inv
            have hefr : (e (f_dih (DihedralGroup.sr i))).right = h_inv := by
              change (e (b * a ^ i.val)).right = h_inv
              rw [map_mul, map_pow, eb_eq, ea_eq, ← map_pow,
                SemidirectProduct.mul_right, SemidirectProduct.right_inr,
                SemidirectProduct.right_inl, mul_one]
            rw [hefr] at hright
            exfalso
            have h_inv_eq : h_inv = (h_triv ^ (Multiplicative.toAdd j).val)⁻¹ := by
              have := mul_left_cancel (a := h_triv ^ (Multiplicative.toAdd j).val)
                (b := h_inv) (c := (h_triv ^ (Multiplicative.toAdd j).val)⁻¹)
                (by rw [hright, mul_inv_cancel])
              exact this
            have hφ_hinv_1 : φ h_inv = 1 := by
              rw [h_inv_eq, map_inv, map_pow, hφ_triv]; simp
            have h1 : n₀ = n₀⁻¹ := by
              have := hφ_inv n₀; rw [hφ_hinv_1] at this; simpa using this
            have h_n₀_sq : n₀ ^ 2 = 1 := by
              rw [sq]; conv_lhs => lhs; rw [h1]
              exact inv_mul_cancel n₀
            have h_ord_dvd : orderOf n₀ ∣ 2 := orderOf_dvd_of_pow_eq_one h_n₀_sq
            rw [hn₀_ord] at h_ord_dvd
            exact absurd (Nat.le_of_dvd (by norm_num) h_ord_dvd) (by omega)
        -- f bijective by cardinality
        have hbij : Function.Bijective f :=
          (Fintype.bijective_iff_injective_and_card f).mpr
            ⟨hinj, by
              rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
                card_fourP_V, hG]⟩
        right; right; right; right
        exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

/-- `IsClassif` packaging for `p ≡ 1 [MOD 4]`. -/
theorem fourP_isClassif_mod1 {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (c : (ZMod p)ˣ) (hcsq : c ^ 2 = -1) :
    IsClassif (4 * p) (rep5 (fourP_I p) (fourP_II p) (fourP_III p)
      (fourP_IV p c (by rw [show (4 : ℕ) = 2 * 2 from by ring, pow_mul, hcsq, neg_one_sq]))
      (fourP_V p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hp2 : p ≠ 2 := by
    intro h; rw [h] at hmod; norm_num at hmod
  have hp1 : 2 < p := by
    have := hp.two_le; omega
  have h_neg1_ne_one : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have h_eq_mod : (-1 : ZMod p) = (1 : ZMod p) := by
      simpa using congrArg Units.val h
    have h2 : (2 : ZMod p) = 0 := by
      calc
        (2 : ZMod p) = (1 : ZMod p) - (-1 : ZMod p) := by ring
        _ = (1 : ZMod p) - (1 : ZMod p) := by rw [h_eq_mod]
        _ = 0 := by ring
    have hp_dvd_2 : p ∣ 2 := ((ZMod.natCast_eq_zero_iff 2 p).mp h2)
    have h_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd_2
    have := hp.two_le
    omega
  let hc : c ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from by ring, pow_mul, hcsq, neg_one_sq]
  have hc1 : c ≠ 1 := by
    intro hc1
    rw [hc1, one_pow] at hcsq
    exact h_neg1_ne_one hcsq.symm
  have hcne : c ≠ -1 := by
    intro hcne
    rw [hcne, show ((-1 : (ZMod p)ˣ) ^ 2) = (1 : (ZMod p)ˣ) by simp] at hcsq
    exact h_neg1_ne_one hcsq.symm
  let hcomplete1 : ∀ (G : Type) [Group G], Nat.card G = 4 * p → Nonempty (G ≃* fourP_I p) ∨
      Nonempty (G ≃* fourP_II p) ∨ Nonempty (G ≃* fourP_III p) ∨
      Nonempty (G ≃* fourP_IV p c hc) ∨ Nonempty (G ≃* fourP_V p) := by
    intro G _ hG
    haveI : Finite G := Nat.finite_of_card_ne_zero (by
      rw [hG]; exact mul_ne_zero (by norm_num) hp.pos.ne')
    exact fourP_classification_mod1 hp hmod c hcsq hG
  exact isClassif_five (fourP_I p) (fourP_II p) (fourP_III p)
    (fourP_IV p c hc) (fourP_V p)
    (card_fourP_I (p := p)) (card_fourP_II (p := p)) (card_fourP_III (p := p) hp2)
    (card_fourP_IV (p := p) c hc) (card_fourP_V (p := p))
    hcomplete1
    (fourP_I_ne_II (p := p) hp2) (fourP_I_ne_III (p := p) hp2)
    (fourP_I_ne_IV (p := p) c hc hc1) (fourP_I_ne_V (p := p) hp1)
    (fourP_II_ne_III (p := p) hp2) (fourP_II_ne_IV (p := p) c hc hc1) (fourP_II_ne_V (p := p) hp1)
    (fourP_III_ne_IV (p := p) c hc hcne)
    (fourP_III_ne_V (p := p) hp2) (fourP_IV_ne_V (p := p) c hc hc1 hp2)

end Smallgroups.UsefulTheorems
