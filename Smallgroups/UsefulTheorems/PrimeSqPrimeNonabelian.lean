/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeSqPrimeAbelian
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Mathlib.Data.Nat.Totient

/-!
# Groups of order `p² · 3` with `3 ∤ p − 1` and `p > 3`: three isomorphism classes
-/

namespace Smallgroups.UsefulTheorems

open SemidirectProduct

/-! ### τ₀ -/

def psqPrimeTau (p : ℕ) : MulAut (ElemAbelianRep p) where
  toFun x := (x.2⁻¹, x.1 * x.2⁻¹)
  invFun x := (x.2 * x.1⁻¹, x.1⁻¹)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by
    ext
    · exact mul_inv x.2 y.2
    · change x.1 * y.1 * (x.2 * y.2)⁻¹ = x.1 * x.2⁻¹ * (y.1 * y.2⁻¹)
      rw [mul_inv x.2 y.2]
      simp only [mul_assoc, mul_left_comm]

@[simp] theorem psqPrimeTau_apply (p : ℕ) (x : ElemAbelianRep p) :
    psqPrimeTau p x = (x.2⁻¹, x.1 * x.2⁻¹) := rfl

theorem psqPrimeTau_cube (p : ℕ) : psqPrimeTau p ^ 3 = 1 := by
  have h3 : (3 : ℕ) = 2 + 1 := by omega
  ext ⟨a, b⟩
  · change (((psqPrimeTau p) ^ 3) (a, b)).1 = (a, b).1
    rw [h3, pow_succ, pow_two]
    change (psqPrimeTau p (psqPrimeTau p (psqPrimeTau p (a, b)))).1 = a
    simp only [psqPrimeTau_apply]; group
  · change (((psqPrimeTau p) ^ 3) (a, b)).2 = (a, b).2
    rw [h3, pow_succ, pow_two]
    change (psqPrimeTau p (psqPrimeTau p (psqPrimeTau p (a, b)))).2 = b
    simp only [psqPrimeTau_apply]; group

/-! ### Action homomorphism and representative -/

noncomputable def psqPrimeActionHom (p : ℕ) :
    Multiplicative (ZMod 3) →* MulAut (ElemAbelianRep p) :=
  MonoidHom.mk' (fun x => psqPrimeTau p ^ (Multiplicative.toAdd x).val)
    (fun a b => pow_val_add (psqPrimeTau_cube p) a.toAdd b.toAdd)

@[simp] theorem psqPrimeActionHom_gen (p : ℕ) :
    psqPrimeActionHom p (Multiplicative.ofAdd 1) = psqPrimeTau p := by
  change psqPrimeTau p ^ ((1 : ZMod 3).val) = psqPrimeTau p
  simp [show (1 : ZMod 3).val = 1 from by decide]

noncomputable abbrev psqPrimeNonabRep (p : ℕ) : Type :=
  ElemAbelianRep p ⋊[psqPrimeActionHom p] CyclicRep 3

theorem card_psqPrimeNonabRep {p : ℕ} (hp : p ≠ 0) :
    Nat.card (psqPrimeNonabRep p) = p ^ 2 * 3 := by
  haveI : NeZero p := ⟨hp⟩
  rw [SemidirectProduct.card, card_elemAbelianRep hp,
    card_cyclicRep (by norm_num : (3 : ℕ) ≠ 0)]

theorem psqPrimeNonabRep_not_comm {p : ℕ} (hp : p.Prime) (_ : ¬ (3 : ℕ) ∣ p - 1) :
    ¬ ∀ a b : psqPrimeNonabRep p, a * b = b * a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have key := h (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 3)))
    (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod p), 1))
  have hleft := congrArg SemidirectProduct.left key
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
    SemidirectProduct.right_inr, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, psqPrimeActionHom_gen,
    psqPrimeTau_apply, map_one, one_mul, mul_one] at hleft
  have h1 : (1 : Multiplicative (ZMod p))⁻¹ = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa using congrArg Prod.fst hleft
  have : (1 : Multiplicative (ZMod p))⁻¹ = Multiplicative.ofAdd (1 : ZMod p) := h1
  rw [inv_one] at this
  have h2 : Multiplicative.toAdd (1 : Multiplicative (ZMod p)) =
    Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p)) := congrArg _ this
  simp only [toAdd_one, toAdd_ofAdd] at h2
  exact one_ne_zero h2.symm

/-! ### Triviality on cyclic P -/

theorem aut_eq_one_of_cyclic_psq {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hqp1 : ¬ q ∣ p - 1)
    {P : Type*} [Group P] [Finite P] (hP : Nat.card P = p ^ 2) [IsCyclic P]
    (α : MulAut P) (hα : α ^ q = 1) : α = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcardH : Nat.card (Subgroup.zpowers α) ∣ q := by
    rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hα
  obtain ⟨n, hn⟩ : ∃ n, Nat.card (Subgroup.zpowers α) = q ^ n := by
    rcases (Nat.dvd_prime hq).mp hcardH with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  haveI hHp : IsPGroup q (Subgroup.zpowers α) := IsPGroup.of_card hn
  let F : Subgroup P :=
    { carrier := {x | α x = x}
      one_mem' := map_one α
      mul_mem' := fun ha hb => by
        simp only [Set.mem_setOf_eq] at *; rw [map_mul, ha, hb]
      inv_mem' := fun ha => by
        simp only [Set.mem_setOf_eq] at *; rw [map_inv, ha] }
  have hFset : MulAction.fixedPoints (Subgroup.zpowers α) P = (F : Set P) := by
    ext x
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨α, Subgroup.mem_zpowers α⟩
    · intro hx g
      have hαx : α x = x := hx
      have hstab : (g : MulAut P) ∈ MulAction.stabilizer (MulAut P) x :=
        Subgroup.zpowers_le.mpr
          (MulAction.mem_stabilizer_iff.mpr (show α • x = x from hαx)) g.2
      exact MulAction.mem_stabilizer_iff.mp hstab
  have hmod : p ^ 2 ≡ Nat.card F [MOD q] := by
    have h := hHp.card_modEq_card_fixedPoints P
    rw [hP] at h; rwa [Nat.card_congr (Equiv.setCongr hFset)] at h
  have hdvd : Nat.card F ∣ p ^ 2 := hP ▸ Subgroup.card_subgroup_dvd_card F
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases k
  · -- |F| = 1: use p-torsion subgroup
    exfalso; rw [pow_zero] at hk
    obtain ⟨g, hg'⟩ := IsCyclic.exists_monoid_generator (α := P)
    have hg : ∀ x, x ∈ Subgroup.zpowers g := fun x =>
      Submonoid.powers_le_zpowers g (hg' x)
    have hgord : orderOf g = p ^ 2 := by
      have htop : Subgroup.zpowers g = ⊤ := by
        ext x; exact ⟨fun _ => Subgroup.mem_top x, fun _ => hg x⟩
      rw [← Nat.card_zpowers, htop, Subgroup.card_top, hP]
    obtain ⟨m, hm⟩ : ∃ m : ℤ, α g = g ^ m := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (α g))
      exact ⟨k, hk.symm⟩
    have hm_iter : ∀ n : ℕ, (α ^ n : MulAut P) g = g ^ m ^ n := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        have : (α ^ (n + 1) : MulAut P) g = (α ^ n : MulAut P) (α g) := by
          rw [pow_succ, MulAut.mul_def]; rfl
        rw [this, hm, map_zpow, ih, ← zpow_mul, pow_succ]
    have hmq_eq : g ^ (m ^ q) = g := by
      have := hm_iter q; rw [hα] at this; simpa using this.symm
    -- m^q ≡ 1 (mod p²)
    have hmq_dvd : (↑(p ^ 2) : ℤ) ∣ m ^ q - 1 := by
      have h1 : g ^ (m ^ q - 1) = 1 := by
        rw [zpow_sub, hmq_eq, zpow_one, mul_inv_cancel]
      have hord := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rwa [hgord, Nat.cast_pow] at hord
    -- m^q ≡ 1 (mod p)
    have hmp_dvd : (↑p : ℤ) ∣ m ^ q - 1 := by
      have h1 : (↑p : ℤ) ∣ ↑(p ^ 2) := by push_cast; exact dvd_pow_self _ (by omega)
      exact dvd_trans h1 hmq_dvd
    have hmp_mod : m ^ q ≡ 1 [ZMOD (p : ℕ)] := by
      rw [Int.modEq_iff_dvd]
      rw [show (1 : ℤ) - m ^ q = -(m ^ q - 1) from by ring]
      exact dvd_neg.mpr hmp_dvd
    -- m ≡ 1 (mod p)
    have hm1 : m ≡ 1 [ZMOD (p : ℕ)] := by
      have hmp' : (m : ZMod p) ^ q = 1 := by
        rw [← Int.cast_pow, ← Int.cast_one, ZMod.intCast_eq_intCast_iff']
        exact hmp_mod
      have hm_ne : (m : ZMod p) ≠ 0 := by
        intro h0; rw [h0, zero_pow hq.ne_zero] at hmp'
        exact zero_ne_one hmp'
      set u : (ZMod p)ˣ := Units.mk0 (m : ZMod p) hm_ne
      have huq : u ^ q = 1 := Units.ext hmp'
      have hcard_units : Nat.card (ZMod p)ˣ = p - 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
      have h2 : orderOf u ∣ p - 1 := hcard_units ▸ orderOf_dvd_natCard u
      have h1 : orderOf u = 1 :=
        Nat.eq_one_of_dvd_coprimes ((hq.coprime_iff_not_dvd.mpr hqp1).symm)
          h2 (orderOf_dvd_of_pow_eq_one huq)
      have hu1 : (u : ZMod p) = 1 := Units.val_eq_one.mpr (orderOf_eq_one_iff.mp h1)
      rw [show (u : ZMod p) = (m : ZMod p) from rfl,
        ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub,
        ZMod.intCast_zmod_eq_zero_iff_dvd] at hu1
      have : (↑p : ℤ) ∣ 1 - m := by
        rw [show (1 : ℤ) - m = -(m - 1) from by ring]
        exact dvd_neg.mpr hu1
      exact Int.modEq_iff_dvd.mpr this
    -- α fixes g^p
    have hfix_gp : α (g ^ (p : ℤ)) = g ^ (p : ℤ) := by
      rw [map_zpow, hm, ← zpow_mul, zpow_eq_zpow_iff_modEq, hgord]
      obtain ⟨c, hc⟩ : (p : ℤ) ∣ m - 1 := Int.modEq_iff_dvd.mp hm1.symm
      show m * ↑p ≡ ↑p [ZMOD (↑(p ^ 2))]
      rw [show (↑(p ^ 2) : ℤ) = ↑p * ↑p from by push_cast; ring]
      rw [Int.modEq_iff_dvd, show (↑p : ℤ) - m * ↑p = -((m - 1) * ↑p) from by ring, hc,
        show -(↑p * c * ↑p) = -(c) * (↑p * ↑p) from by ring]
      exact dvd_mul_left _ _
    -- g^p ≠ 1
    have hgp_ne : g ^ (p : ℤ) ≠ 1 := by
      intro h
      have hord := orderOf_dvd_iff_zpow_eq_one.mpr h
      rw [hgord] at hord
      have h1 : p ^ 2 ∣ p := by exact_mod_cast hord
      exact absurd (Nat.le_of_dvd hp.pos h1) (by nlinarith [hp.two_le])
    -- g^p ∈ F, |F| ≥ 2, contradiction
    haveI : Nontrivial F := by
      exact ⟨⟨⟨g ^ (p : ℤ), hfix_gp⟩, ⟨1, F.one_mem⟩, by
        simp only [ne_eq, Subtype.mk.injEq]; exact hgp_ne⟩⟩
    have : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  · -- |F| = p: gives q ∣ p − 1
    exfalso; apply hqp1
    rw [pow_one] at hk; rw [hk] at hmod
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    exact (Nat.modEq_iff_dvd' hp.one_le).mp
      (Nat.ModEq.cancel_left_of_coprime
        (by rwa [Nat.coprime_comm] at hcop)
        (by rw [mul_one, ← pow_two]; exact hmod)).symm
  · -- |F| = p²: α = 1
    have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hk, hP])
    ext x
    have hxF : x ∈ F := hFtop ▸ Subgroup.mem_top x
    exact hxF

/-! ### Distinctness -/

theorem psq_prime_nonab_distinct_ab1 {p : ℕ} (hp : p.Prime) (hp3 : ¬ (3 : ℕ) ∣ p - 1) :
    ¬ Nonempty (psqPrimeRep1 p 3 ≃* psqPrimeNonabRep p) :=
  isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b)
    (psqPrimeNonabRep_not_comm hp hp3)

theorem psq_prime_nonab_distinct_ab2 {p : ℕ} (hp : p.Prime) (hp3 : ¬ (3 : ℕ) ∣ p - 1) :
    ¬ Nonempty (psqPrimeRep2 p 3 ≃* psqPrimeNonabRep p) :=
  isEmpty_mulEquiv_of_comm_noncomm (fun a b => mul_comm a b)
    (psqPrimeNonabRep_not_comm hp hp3)

/-! ### Conjugacy of order-3 automorphisms on (ℤ/p)² -/

private lemma ofAdd_pow_nat (p : ℕ) [NeZero p] (c : ZMod p) (n : ℕ) :
    (Multiplicative.ofAdd c : Multiplicative (ZMod p)) ^ n = Multiplicative.ofAdd (↑n * c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← ofAdd_add, Nat.cast_succ, add_mul, one_mul]

private lemma ofAdd_one_pow (p : ℕ) [NeZero p] (n : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod p)) ^ n = Multiplicative.ofAdd (↑n : ZMod p) := by
  rw [ofAdd_pow_nat, mul_one]

private lemma elemAbelianRep_pow_eq (p : ℕ) [NeZero p] (s : Multiplicative (ZMod p)) :
    ((s, 1) : ElemAbelianRep p) =
      ((Multiplicative.ofAdd 1, 1) : ElemAbelianRep p) ^ (Multiplicative.toAdd s).val := by
  ext
  · simp only [Prod.pow_fst, ofAdd_one_pow, ZMod.natCast_zmod_val,
      ofAdd_toAdd]
  · simp only [Prod.pow_snd, one_pow]

private lemma elemAbelianRep_pow_eq' (p : ℕ) [NeZero p] (s : Multiplicative (ZMod p)) :
    ((1, s) : ElemAbelianRep p) =
      ((1, Multiplicative.ofAdd 1) : ElemAbelianRep p) ^ (Multiplicative.toAdd s).val := by
  ext
  · simp only [Prod.pow_fst, one_pow]
  · simp only [Prod.pow_snd, ofAdd_one_pow, ZMod.natCast_zmod_val,
      ofAdd_toAdd]

private lemma monoidHom_elemAbelianRep_ext {p : ℕ} [NeZero p] {M : Type*} [Monoid M]
    (f g : ElemAbelianRep p →* M)
    (h1 : f (Multiplicative.ofAdd 1, 1) = g (Multiplicative.ofAdd 1, 1))
    (h2 : f (1, Multiplicative.ofAdd 1) = g (1, Multiplicative.ofAdd 1)) :
    f = g := by
  ext ⟨x1, x2⟩
  have hdecomp : ((x1, x2) : ElemAbelianRep p) = (x1, 1) * (1, x2) := by ext <;> simp
  rw [hdecomp, map_mul, map_mul]
  congr 1
  · rw [elemAbelianRep_pow_eq, map_pow, map_pow, h1]
  · rw [elemAbelianRep_pow_eq', map_pow, map_pow, h2]

private noncomputable def conjTheta (p : ℕ) [NeZero p] [Fact (Nat.Prime p)]
    (a b : ZMod p) (hb : b ≠ 0) : MulAut (ElemAbelianRep p) where
  toFun x := (Multiplicative.ofAdd (x.1.toAdd + a * x.2.toAdd),
              Multiplicative.ofAdd (b * x.2.toAdd))
  invFun x := (Multiplicative.ofAdd (x.1.toAdd - a * b⁻¹ * x.2.toAdd),
               Multiplicative.ofAdd (b⁻¹ * x.2.toAdd))
  left_inv x := by
    ext
    · simp only [ofAdd_add, ofAdd_toAdd, toAdd_mul, toAdd_ofAdd, ofAdd_sub, toAdd_div]
      calc
        x.1.toAdd + a * x.2.toAdd - a * b⁻¹ * (b * x.2.toAdd)
            = x.1.toAdd + a * x.2.toAdd - a * (b⁻¹ * b) * x.2.toAdd := by ring
        _ = x.1.toAdd + a * x.2.toAdd - a * 1 * x.2.toAdd := by field_simp [hb]
        _ = x.1.toAdd := by ring
    · simp [toAdd_ofAdd]; field_simp [hb]
  right_inv x := by
    ext
    · simp [toAdd_ofAdd]; ring
    · simp [toAdd_ofAdd]; field_simp [hb]
  map_mul' x y := by
    ext
    · simp [toAdd_ofAdd, toAdd_mul]; ring
    · simp [toAdd_ofAdd, toAdd_mul]; ring

/-- Any non-trivial homomorphism `ℤ/3 → Aut((ℤ/p)²)` with `3 ∤ p-1` gives a semidirect product
isomorphic to `psqPrimeNonabRep p`. -/
private theorem semidirect_elem_nonab_iso (p : ℕ) (hp : Nat.Prime p) (hp3 : ¬ (3 : ℕ) ∣ p - 1)
    (hp3' : p ≠ 3)
    (φ' : Multiplicative (ZMod 3) →* MulAut (ElemAbelianRep p)) (hφ' : φ' ≠ 1) :
    Nonempty (ElemAbelianRep p ⋊[φ'] Multiplicative (ZMod 3) ≃*
      psqPrimeNonabRep p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero (3 : ℕ) := ⟨by omega⟩
  set α := φ' (Multiplicative.ofAdd 1) with hα_def
  have hg3 : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by
    calc
      (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 =
          (Multiplicative.ofAdd (1 : ZMod 3)) ^ 2 * (Multiplicative.ofAdd (1 : ZMod 3)) := by
        rw [pow_succ]
      _ = (Multiplicative.ofAdd (1 : ZMod 3) * Multiplicative.ofAdd (1 : ZMod 3)) *
          Multiplicative.ofAdd (1 : ZMod 3) := by rw [pow_two]
      _ = Multiplicative.ofAdd ((2 : ZMod 3)) * Multiplicative.ofAdd (1 : ZMod 3) := by
        rw [← ofAdd_add]; norm_num
      _ = Multiplicative.ofAdd (((2 : ZMod 3) + (1 : ZMod 3))) := by rw [ofAdd_add]
      _ = 1 := by
        have h3zero : (3 : ZMod 3) = 0 :=
          CharP.cast_eq_zero (ZMod 3) 3
        calc
          Multiplicative.ofAdd (((2 : ZMod 3) + (1 : ZMod 3)))
              = Multiplicative.ofAdd ((3 : ZMod 3)) := by ring_nf
          _ = Multiplicative.ofAdd (0 : ZMod 3) := by rw [h3zero]
          _ = 1 := by simp
  have hα3 : α ^ 3 = 1 := by
    rw [hα_def, ← map_pow, hg3, map_one]
  have h_ord : orderOf (Multiplicative.ofAdd (1 : ZMod 3)) = 3 := by
    have hpos : orderOf (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1 := by
      intro h
      have h1 := orderOf_eq_one_iff.mp h
      have : (1 : ZMod 3) = 0 := by
        simpa [ofAdd_add] using congrArg Multiplicative.toAdd h1
      norm_num at this
    have h_dvd : orderOf (Multiplicative.ofAdd (1 : ZMod 3)) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one hg3
    rcases (Nat.dvd_prime Nat.prime_three).mp h_dvd with (h | h)
    · exact absurd h hpos
    · exact h
  have htop : Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod 3)) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by
      rw [Nat.card_zpowers, h_ord]
      simp)
  have hα_ne : α ≠ 1 := by
    intro h
    apply hφ'
    refine MonoidHom.ext fun k => ?_
    have hk : k ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod 3)) := by
      rw [htop]; exact Subgroup.mem_top k
    rcases Subgroup.mem_zpowers_iff.mp hk with ⟨n, rfl⟩
    calc
      φ' ((Multiplicative.ofAdd (1 : ZMod 3)) ^ n) =
          (φ' (Multiplicative.ofAdd (1 : ZMod 3))) ^ n := by rw [map_zpow]
      _ = α ^ n := by rw [hα_def]
      _ = 1 ^ n := by rw [h]
      _ = 1 := by simp
      _ = (1 : MonoidHom (Multiplicative (ZMod 3)) (MulAut (ElemAbelianRep p)))
            ((Multiplicative.ofAdd (1 : ZMod 3)) ^ n) := by simp
  -- Fixed-point-free: {x | α x = x} = {1}
  have h_abel : CommGroup (ElemAbelianRep p) := by infer_instance
  have hfpf : ∀ x : ElemAbelianRep p, α x = x → x = 1 := by
    let F : Subgroup (ElemAbelianRep p) :=
      { carrier := {x | α x = x}
        one_mem' := map_one α
        mul_mem' := fun ha hb => by
          simp only [Set.mem_setOf_eq] at *; rw [map_mul, ha, hb]
        inv_mem' := fun ha => by
          simp only [Set.mem_setOf_eq] at *; rw [map_inv, ha] }
    suffices hF1 : Nat.card F = 1 by
      intro x hx
      exact Subgroup.mem_bot.mp ((Subgroup.eq_bot_of_card_eq F hF1) ▸ (hx : x ∈ F))
    have hcardH : Nat.card (Subgroup.zpowers α) ∣ 3 := by
      rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hα3
    obtain ⟨n, hn⟩ : ∃ n, Nat.card (Subgroup.zpowers α) = 3 ^ n := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hcardH with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    haveI h3grp : IsPGroup 3 (Subgroup.zpowers α) := IsPGroup.of_card hn
    have hFset : MulAction.fixedPoints (Subgroup.zpowers α) (ElemAbelianRep p) =
        (F : Set (ElemAbelianRep p)) := by
      ext x; rw [MulAction.mem_fixedPoints]; constructor
      · intro h; exact h ⟨α, Subgroup.mem_zpowers α⟩
      · intro hx g
        exact MulAction.mem_stabilizer_iff.mp
          (Subgroup.zpowers_le.mpr
            (MulAction.mem_stabilizer_iff.mpr (show α • x = x from hx)) g.2)
    have hmod : p ^ 2 ≡ Nat.card F [MOD 3] := by
      have h := h3grp.card_modEq_card_fixedPoints (ElemAbelianRep p)
      rw [card_elemAbelianRep hp.ne_zero] at h
      rwa [Nat.card_congr (Equiv.setCongr hFset)] at h
    have hdvd : Nat.card F ∣ p ^ 2 :=
      (card_elemAbelianRep hp.ne_zero) ▸ Subgroup.card_subgroup_dvd_card F
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    interval_cases k
    · rwa [pow_zero] at hk
    · exfalso; apply hp3
      rw [pow_one] at hk; rw [hk] at hmod
      exact (Nat.modEq_iff_dvd' hp.one_le).mp
        (Nat.ModEq.cancel_left_of_coprime
          (Nat.coprime_comm.mp ((Nat.coprime_primes hp Nat.prime_three).mpr (by omega)))
          (by rw [mul_one, ← pow_two]; exact hmod)).symm
    · have hFtop := Subgroup.eq_top_of_card_eq F (by rw [hk, card_elemAbelianRep hp.ne_zero])
      have h_all : ∀ x, α x = x := by
        intro x; have := hFtop ▸ Subgroup.mem_top x; simpa [F] using this
      have h_alpha_one : α = 1 := by
        apply MulEquiv.ext; intro x; exact h_all x
      exfalso; exact hα_ne h_alpha_one
  -- α²(x) * α(x) * x = 1
  have hrel : ∀ x : ElemAbelianRep p, α (α x) * α x * x = 1 := by
    intro x
    apply hfpf
    have h3x : α (α (α x)) = x := by
      have h := DFunLike.congr_fun hα3 x
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two] at h
      rwa [MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply] at h
    calc α (α (α x) * α x * x)
        = α (α (α x)) * α (α x) * α x := by rw [map_mul, map_mul]
      _ = x * α (α x) * α x := by rw [h3x]
      _ = α (α x) * α x * x := by
          simp only [mul_comm, mul_left_comm]
  -- Extract matrix entries from α(e₁)
  set a := (α (Multiplicative.ofAdd 1, 1)).1.toAdd
  set b := (α (Multiplicative.ofAdd 1, 1)).2.toAdd
  have hb : b ≠ 0 := by
    intro hb0
    -- If b = 0, α(e₁) = (ofAdd a, 1), so α preserves {(x, 1)}.
    -- The restriction to {(x, 1)} ≅ ℤ/p has order dividing 3, but 3 ∤ p-1,
    -- so it's trivial, meaning α(e₁) = e₁, contradicting hfpf.
    have hα_e1 : α (Multiplicative.ofAdd 1, 1) =
        ((Multiplicative.ofAdd a, 1) : ElemAbelianRep p) := by
      apply Prod.ext
      · exact (ofAdd_toAdd _).symm
      · have h2 : (α (Multiplicative.ofAdd 1, 1)).2 = Multiplicative.ofAdd b :=
          (ofAdd_toAdd _).symm
        rw [h2, hb0, ofAdd_zero]
    -- α(e₁) is in the first factor, so the restriction of α to the first factor
    -- is multiplication by a. Since α³ = 1, a³ = 1.
    have ha3 : a ^ 3 = 1 := by
      have h_pow : ∀ s : Multiplicative (ZMod p),
          α ((s, 1) : ElemAbelianRep p) =
          ((Multiplicative.ofAdd a, 1) : ElemAbelianRep p) ^
            (Multiplicative.toAdd s).val := by
        intro s; rw [elemAbelianRep_pow_eq, map_pow, hα_e1]
      have h_fst : ∀ c : ZMod p,
          (α ((Multiplicative.ofAdd c, 1) : ElemAbelianRep p)).1 =
          Multiplicative.ofAdd (c * a) := by
        intro c; rw [h_pow, Prod.pow_fst, ofAdd_pow_nat,
          toAdd_ofAdd, ZMod.natCast_zmod_val, mul_comm]
      have h_snd : ∀ c : ZMod p,
          (α ((Multiplicative.ofAdd c, 1) : ElemAbelianRep p)).2 = 1 := by
        intro c; rw [h_pow, Prod.pow_snd, one_pow]
      have h3 := DFunLike.congr_fun hα3
        ((Multiplicative.ofAdd (1 : ZMod p), (1 : Multiplicative (ZMod p))))
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two,
        MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply, hα_e1] at h3
      have h2_eq : α ((Multiplicative.ofAdd a, 1) : ElemAbelianRep p) =
          ((Multiplicative.ofAdd (a * a), 1) : ElemAbelianRep p) :=
        Prod.ext (h_fst a) (h_snd a)
      rw [h2_eq] at h3
      have h3_fst := congrArg Prod.fst h3
      rw [h_fst (a * a)] at h3_fst
      rw [show a ^ 3 = (a * a) * a from by ring]
      exact Multiplicative.ofAdd.injective h3_fst
    -- If a = 1, α fixes e₁, contradicting hfpf
    -- If a ≠ 1, a has order 3 in (ZMod p)ˣ, so 3 ∣ p-1, contradicting hp3
    by_cases ha1 : a = 1
    · exfalso
      have hfix : α ((Multiplicative.ofAdd 1, 1) : ElemAbelianRep p) =
          (Multiplicative.ofAdd 1, 1) := by rw [hα_e1]; simp [ha1]
      have h := hfpf _ hfix
      have h1 : (1 : ZMod p) = 0 := by
        have := congrArg (fun x => Multiplicative.toAdd (Prod.fst x)) h
        simp [toAdd_ofAdd, toAdd_one] at this
      exact one_ne_zero h1
    · apply hp3
      have ha_ne : (a : ZMod p) ≠ 0 := by
        intro h0; rw [h0] at ha3; simp at ha3
      set u : (ZMod p)ˣ := Units.mk0 a ha_ne
      have hu3 : u ^ 3 = 1 := Units.ext ha3
      have hcard_units : Nat.card (ZMod p)ˣ = p - 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
      have hord3 : orderOf u = 3 := by
        have hord_dvd : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
        rcases (Nat.dvd_prime Nat.prime_three).mp hord_dvd with h1 | h3
        · exfalso; apply ha1
          exact Units.val_eq_one.mpr (orderOf_eq_one_iff.mp h1)
        · exact h3
      rw [← hcard_units]; exact hord3 ▸ orderOf_dvd_natCard u
  -- The conjugating automorphism
  set θ := conjTheta p a b hb
  -- θ intertwines τ₀ and α: θ(τ₀ x) = α(θ x) for all x
  have hα_e1_eq : α ((Multiplicative.ofAdd 1, 1) : ElemAbelianRep p) =
      ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) : ElemAbelianRep p) := by
    ext
    · exact (ofAdd_toAdd _).symm
    · exact (ofAdd_toAdd _).symm
  have hα2_e1 : α (α ((Multiplicative.ofAdd 1, 1) : ElemAbelianRep p)) =
      ((Multiplicative.ofAdd (-1 - a), Multiplicative.ofAdd (-b)) : ElemAbelianRep p) := by
    have h1 := hrel ((Multiplicative.ofAdd (1 : ZMod p), 1) : ElemAbelianRep p)
    rw [mul_assoc] at h1
    have h_eq := mul_eq_one_iff_eq_inv.mp h1
    rw [h_eq, hα_e1_eq]
    ext
    · simp [toAdd_ofAdd]; ring
    · simp only [Prod.snd_mul, Prod.snd_inv, ofAdd_neg, mul_one];
  have hintertwine : ∀ x, θ (psqPrimeTau p x) = α (θ x) := by
    suffices h : (θ.toMonoidHom).comp (psqPrimeTau p).toMonoidHom =
        (α.toMonoidHom).comp θ.toMonoidHom from
      fun x => DFunLike.congr_fun h x
    apply monoidHom_elemAbelianRep_ext
    · -- e₁: θ(τ₀(ofAdd 1, 1)) = α(θ(ofAdd 1, 1))
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      have hLHS : θ (psqPrimeTau p ((Multiplicative.ofAdd 1, 1) : ElemAbelianRep p)) =
          ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) : ElemAbelianRep p) := by
        change conjTheta p a b hb (psqPrimeTau p (Multiplicative.ofAdd 1, 1)) = _
        simp only [psqPrimeTau_apply, conjTheta]
        ext <;> simp [toAdd_ofAdd]
      have hRHS : α (θ ((Multiplicative.ofAdd 1, 1) : ElemAbelianRep p)) =
          ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) : ElemAbelianRep p) := by
        have hθ_e1 : θ ((Multiplicative.ofAdd 1, 1) : ElemAbelianRep p) =
            ((Multiplicative.ofAdd 1, 1) : ElemAbelianRep p) := by
          change conjTheta p a b hb _ = _
          simp only [conjTheta]
          ext <;> simp [toAdd_ofAdd, toAdd_one]
        rw [hθ_e1, hα_e1_eq]
      rw [hLHS, hRHS]
    · -- e₂: θ(τ₀(1, ofAdd 1)) = α(θ(1, ofAdd 1))
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      have hLHS : θ (psqPrimeTau p ((1, Multiplicative.ofAdd 1) : ElemAbelianRep p)) =
          ((Multiplicative.ofAdd (-1 - a), Multiplicative.ofAdd (-b)) : ElemAbelianRep p) := by
        change conjTheta p a b hb (psqPrimeTau p (1, Multiplicative.ofAdd 1)) = _
        simp only [psqPrimeTau_apply, conjTheta]
        ext <;> simp [toAdd_ofAdd, toAdd_inv, toAdd_mul]; ring
      have hRHS : α (θ ((1, Multiplicative.ofAdd 1) : ElemAbelianRep p)) =
          ((Multiplicative.ofAdd (-1 - a), Multiplicative.ofAdd (-b)) : ElemAbelianRep p) := by
        have hθ_e2 : θ ((1, Multiplicative.ofAdd 1) : ElemAbelianRep p) =
            ((Multiplicative.ofAdd a, Multiplicative.ofAdd b) : ElemAbelianRep p) := by
          change conjTheta p a b hb _ = _
          simp only [conjTheta]
          ext <;> simp [toAdd_ofAdd]
        rw [hθ_e2, ← hα_e1_eq, hα2_e1]
      rw [hLHS, hRHS]
  -- Build the isomorphism via semidirectProductCongrConj
  have h_conj_val : (MulAut.conj θ.symm) α = psqPrimeTau p := by
    apply MulEquiv.ext
    intro x
    apply Prod.ext
    · have h := calc
        ((MulAut.conj θ.symm) α) x = (θ.symm * α * θ) x := rfl
        _ = θ.symm (α (θ x)) := rfl
        _ = θ.symm (θ (psqPrimeTau p x)) := by rw [hintertwine x]
        _ = psqPrimeTau p x := by simp
      simpa using congrArg (·.1) h
    · have h := calc
        ((MulAut.conj θ.symm) α) x = (θ.symm * α * θ) x := rfl
        _ = θ.symm (α (θ x)) := rfl
        _ = θ.symm (θ (psqPrimeTau p x)) := by rw [hintertwine x]
        _ = psqPrimeTau p x := by simp
      simpa using congrArg (·.2) h
  have h_actions_eq : (MulAut.conj θ.symm).toMonoidHom.comp φ' = psqPrimeActionHom p := by
    refine MonoidHom.ext fun k => ?_
    have hk : k ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod 3)) := by
      rw [htop]; exact Subgroup.mem_top k
    rcases Subgroup.mem_zpowers_iff.mp hk with ⟨n, rfl⟩
    calc
      ((MulAut.conj θ.symm).toMonoidHom.comp φ') ((Multiplicative.ofAdd (1 : ZMod 3)) ^ n)
          = (MulAut.conj θ.symm) (φ' ((Multiplicative.ofAdd (1 : ZMod 3)) ^ n)) := rfl
      _ = (MulAut.conj θ.symm) ((φ' (Multiplicative.ofAdd (1 : ZMod 3))) ^ n) := by rw [map_zpow]
      _ = (MulAut.conj θ.symm) (α ^ n) := by rw [hα_def]
      _ = ((MulAut.conj θ.symm) α) ^ n := by rw [map_zpow]
      _ = (psqPrimeTau p) ^ n := by rw [h_conj_val]
      _ = psqPrimeActionHom p ((Multiplicative.ofAdd (1 : ZMod 3)) ^ n) := by
        rw [MonoidHom.map_zpow, psqPrimeActionHom_gen]
  exact ⟨(semidirectProductCongrConj θ.symm).trans
    (semidirectProductCongr_eq h_actions_eq)⟩

/-! ### Exhaustiveness and classification -/

/-- Three-way classification for order `p² · 3` with `3 ∤ p − 1`, `p ≠ 3`. -/
theorem psq_prime_nonab_classification {p : ℕ} (hp : p.Prime) (hp3 : ¬ (3 : ℕ) ∣ p - 1)
    (hpdvd : ¬ p ∣ 2) (hpq : p ≠ 3) {G : Type*} [Group G] [Finite G]
    {N : ℕ} (hN : p ^ 2 * 3 = N) (hG : Nat.card G = N) :
    Nonempty (G ≃* psqPrimeRep1 p 3) ∨
    Nonempty (G ≃* psqPrimeRep2 p 3) ∨
    Nonempty (G ≃* psqPrimeNonabRep p) := by
  subst hN
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p 3 :=
    (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  obtain ⟨P, K, φ, _, hPcard, hKcard, ⟨e⟩⟩ :=
    psq_semidirectProduct hp Nat.prime_three hpq hpdvd hG
  have eK : (↥K) ≃* Multiplicative (ZMod 3) :=
    (prime_classification Nat.prime_three hKcard).some
  rcases prime_sq_classification hPcard with hPcyc | hPelem
  · -- P cyclic: action trivial
    obtain ⟨eP⟩ := hPcyc
    have hφtriv : φ = 1 := MonoidHom.ext fun k => by
      haveI : IsCyclic P := isCyclic_of_surjective eP.symm eP.symm.surjective
      have hk3 : k ^ 3 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (hKcard ▸ orderOf_dvd_natCard k)
      exact aut_eq_one_of_cyclic_psq hp Nat.prime_three hpq hp3 hPcard (φ k)
        (by rw [← map_pow, hk3, map_one])
    exact Or.inl ⟨e.trans <| (semidirectProductCongr_eq hφtriv).trans
      SemidirectProduct.mulEquivProd |>.trans <|
      (MulEquiv.prodCongr eP eK).trans (crtProd (p ^ 2) 3 (hcop.pow_left 2))⟩
  · -- P elementary abelian
    obtain ⟨eP⟩ := hPelem
    by_cases hφtriv : ∀ k, φ k = 1
    · -- Trivial action: abelian
      exact Or.inr (Or.inl ⟨e.trans <|
        (semidirectProductCongr_eq (MonoidHom.ext hφtriv)).trans
        SemidirectProduct.mulEquivProd |>.trans <|
        (MulEquiv.prodCongr eP eK).trans <|
        MulEquiv.prodAssoc.trans
          (MulEquiv.prodCongr (MulEquiv.refl _) (crtProd p 3 hcop))⟩)
    · -- Non-trivial action: the nonabelian class
      push Not at hφtriv
      obtain ⟨k₀, hk₀⟩ := hφtriv
      -- Transport action to ElemAbelianRep p via eP and eK
      let φ_trans : Multiplicative (ZMod 3) →* MulAut (ElemAbelianRep p) :=
        MonoidHom.mk' (fun k' => (eP.symm.trans (φ (eK.symm k'))).trans eP)
          (fun x y => by
            have h_eq : ((eP.symm.trans (φ (eK.symm (x * y)))).trans eP) =
                ((eP.symm.trans (φ (eK.symm x))).trans eP) *
                ((eP.symm.trans (φ (eK.symm y))).trans eP) := by
              apply MulEquiv.ext
              intro n
              apply Prod.ext
              · simp [MulEquiv.trans_apply, MulAut.mul_apply, map_mul, eP.symm_apply_apply]
              · simp [MulEquiv.trans_apply, MulAut.mul_apply, map_mul, eP.symm_apply_apply]
            exact h_eq)
      have hφ_ne : φ_trans ≠ 1 := by
        intro h
        apply hk₀
        have heq : φ_trans (eK k₀) = 1 := by
          simpa using congrArg (fun f => f (eK k₀)) h
        have heq' : (eP.symm.trans (φ k₀)).trans eP = 1 := by
          calc
            (eP.symm.trans (φ k₀)).trans eP =
              (eP.symm.trans (φ (eK.symm (eK k₀)))).trans eP := by rw [eK.symm_apply_apply]
            _ = φ_trans (eK k₀) := by rw [MonoidHom.mk'_apply]
            _ = 1 := heq
        ext x
        have hx := congrArg (fun (f : MulAut (ElemAbelianRep p)) => f (eP x)) heq'
        simpa [MulEquiv.trans_apply, eP.symm_apply_apply] using hx
      exact Or.inr (Or.inr ⟨e.trans <|
        (semidirectProductCongr eP eK (fun h => by
          unfold φ_trans
          apply MonoidHom.ext
          intro x
          apply Prod.ext
          · simp [MonoidHom.comp_apply, MonoidHom.mk'_apply,
              eK.symm_apply_apply, eP.symm_apply_apply]
          · simp [MonoidHom.comp_apply, MonoidHom.mk'_apply,
              eK.symm_apply_apply, eP.symm_apply_apply])) |>.trans <|
        (semidirect_elem_nonab_iso p hp hp3 hpq φ_trans hφ_ne).some⟩)

/-- `IsClassif` packaging for the three classes. -/
theorem psq_prime_nonab_isClassif {p : ℕ} (hp : p.Prime) (hp3 : ¬ (3 : ℕ) ∣ p - 1)
    (hpdvd : ¬ p ∣ 2) (hpq : p ≠ 3) {N : ℕ} (hN : p ^ 2 * 3 = N) :
    IsClassif N (rep3 (psqPrimeRep1 p 3) (psqPrimeRep2 p 3)
      (psqPrimeNonabRep p)) := by
  subst hN
  exact isClassif_three _ _ _
    (card_psqPrimeRep1 hp Nat.prime_three)
    (card_psqPrimeRep2 hp Nat.prime_three)
    (by rw [card_psqPrimeNonabRep hp.ne_zero, mul_comm])
    (fun G _ hG => by
      haveI : Finite G := Nat.finite_of_card_ne_zero
        (by rw [hG]; exact Nat.mul_ne_zero (pow_ne_zero 2 hp.ne_zero) (by norm_num))
      exact psq_prime_nonab_classification hp hp3 hpdvd hpq rfl hG)
    (psq_prime_distinct hp Nat.prime_three)
    (psq_prime_nonab_distinct_ab1 hp hp3)
    (psq_prime_nonab_distinct_ab2 hp hp3)

end Smallgroups.UsefulTheorems
