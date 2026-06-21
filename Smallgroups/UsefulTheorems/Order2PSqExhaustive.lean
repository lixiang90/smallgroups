/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PSq
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.SemidirectProductClassify
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Exhaustiveness for order `2 p²`: the ℤ/p² Sylow case

Every group of order `2 p²` (`p` an odd prime) is a semidirect product `N ⋊[ψ] ℤ/2` with `N` the
abelian Sylow-`p` subgroup (order `p²`, so `≅ ℤ/p²` or `(ℤ/p)²`). This file establishes that
reduction and classifies the involution in the **cyclic Sylow** (`ℤ/p²`) case:
`ψ(1) = ±1`, distributing `G` among the cyclic group `ℤ/2p²` (trivial action, `R1`) and the
dihedral group `D_{p²}` (inversion, `R3`).
-/

namespace Smallgroups.UsefulTheorems

open SemidirectProduct

variable {G : Type*} [Group G] {p : ℕ}

/-- **Reduction.** A group of order `2 p²` (`p ≠ 2` prime) is a semidirect product of `ℤ/p²` or
`(ℤ/p)²` by `ℤ/2`. -/
theorem order2psq_semidirect [Fact p.Prime] (hp2 : p ≠ 2) [Finite G]
    (hG : Nat.card G = 2 * p ^ 2) :
    (∃ φ : Multiplicative (ZMod 2) →* MulAut (CyclicRep (p ^ 2)),
        Nonempty (G ≃* SemidirectProduct (CyclicRep (p ^ 2)) (Multiplicative (ZMod 2)) φ)) ∨
      (∃ φ : Multiplicative (ZMod 2) →* MulAut (ElemAbelianRep p),
        Nonempty (G ≃* SemidirectProduct (ElemAbelianRep p) (Multiplicative (ZMod 2)) φ)) := by
  have hp : p.Prime := Fact.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, K, φ, _, hPcard, hKcard, ⟨e⟩⟩ :=
    psq_semidirectProduct hp Nat.prime_two hp2 (by simpa using hp.ne_one) (by rw [hG]; ring)
  have eK : (K : Type _) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hKcard (by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  rcases prime_sq_classification (G := (P : Type _)) hPcard with hP | hP
  · exact Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' hP.some eK)⟩⟩
  · exact Or.inr ⟨_, ⟨e.trans (SemidirectProduct.congr' hP.some eK)⟩⟩

/-!
### Number-theoretic lemma
In `ZMod (p ^ 2)` with `p` an odd prime, `k² = 1` implies `k = ±1`.
-/

theorem square_eq_one_zmod_psq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ZMod (p ^ 2))
    (h : k ^ 2 = 1) : k = 1 ∨ k = -1 := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have h_factor : (k - 1) * (k + 1) = 0 := by
    calc
      (k - 1) * (k + 1) = k ^ 2 - 1 := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring
  -- Lemma: in ZMod(p^2), non-units are exactly multiples of p
  have hp_nonunit_dvd (x : ZMod (p ^ 2)) (hx : ¬ IsUnit x) : (p : ZMod (p ^ 2)) ∣ x := by
    have h_val : (x.val : ZMod (p ^ 2)) = x := ZMod.natCast_zmod_val x
    have hx' : ¬ IsUnit ((x.val : ZMod (p ^ 2))) := by
      simpa [h_val] using hx
    have h_dvd_val : (p : ZMod (p ^ 2)) ∣ (x.val : ZMod (p ^ 2)) := by
      rw [ZMod.isUnit_iff_coprime (x.val) (p ^ 2)] at hx'
      have hp_dvd_val : p ∣ x.val := by
        by_contra! h_not_dvd
        apply hx'
        have hcp : Nat.Coprime (x.val) p :=
          ((hp.coprime_iff_not_dvd.mpr h_not_dvd).symm)
        have hcp_sq : Nat.Coprime (x.val) (p ^ 2) :=
          (Nat.Coprime.pow_left 2 hcp.symm).symm
        exact hcp_sq
      rcases hp_dvd_val with ⟨c, hc⟩
      use (c : ZMod (p ^ 2))
      simp [hc]
    rw [h_val] at h_dvd_val
    exact h_dvd_val
  by_cases h_unit : IsUnit (k - 1)
  · rcases h_unit.exists_right_inv with ⟨inv, hinv⟩
    have h_zero : k + 1 = 0 := by
      calc
        k + 1 = 1 * (k + 1) := by simp
        _ = ((k - 1) * inv) * (k + 1) := by rw [hinv]
        _ = inv * ((k - 1) * (k + 1)) := by ring
        _ = inv * 0 := by rw [h_factor]
        _ = 0 := by simp
    right
    calc
      k = (k + 1) - 1 := by ring
      _ = 0 - 1 := by rw [h_zero]
      _ = -1 := by ring
  · by_cases h_unit' : IsUnit (k + 1)
    · rcases h_unit'.exists_right_inv with ⟨inv, hinv⟩
      have h_zero : k - 1 = 0 := by
        calc
          k - 1 = 1 * (k - 1) := by simp
          _ = ((k + 1) * inv) * (k - 1) := by rw [hinv]
          _ = inv * ((k + 1) * (k - 1)) := by ring
          _ = inv * ((k - 1) * (k + 1)) := by ring
          _ = inv * 0 := by rw [h_factor]
          _ = 0 := by simp
      left
      calc
        k = (k - 1) + 1 := by ring
        _ = 0 + 1 := by rw [h_zero]
        _ = 1 := by simp
    · have hp_dvd_left : (p : ZMod (p ^ 2)) ∣ k - 1 := hp_nonunit_dvd (k - 1) h_unit
      have hp_dvd_right : (p : ZMod (p ^ 2)) ∣ k + 1 := hp_nonunit_dvd (k + 1) h_unit'
      have h_sub : (p : ZMod (p ^ 2)) ∣ (k + 1) - (k - 1) := dvd_sub hp_dvd_right hp_dvd_left
      have h_two_dvd : (p : ZMod (p ^ 2)) ∣ (2 : ZMod (p ^ 2)) := by
        have h_eq : (k + 1) - (k - 1) = (2 : ZMod (p ^ 2)) := by ring
        rw [h_eq] at h_sub
        exact h_sub
      rcases h_two_dvd with ⟨c, hc⟩
      have h_p_sq_zero : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
        calc
          (p : ZMod (p ^ 2)) ^ 2 = (p * p : ZMod (p ^ 2)) := by ring
          _ = ((p * p : ℕ) : ZMod (p ^ 2)) := by norm_num
          _ = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) := by ring_nf
          _ = 0 := CharP.cast_eq_zero (ZMod (p ^ 2)) (p ^ 2)
      have h_2p_zero : (2 * (p : ZMod (p ^ 2))) = 0 := by
        calc
          2 * (p : ZMod (p ^ 2)) = ((p : ZMod (p ^ 2)) * c) * (p : ZMod (p ^ 2)) := by rw [hc]
          _ = (p : ZMod (p ^ 2)) ^ 2 * c := by ring
          _ = 0 * c := by rw [h_p_sq_zero]
          _ = 0 := by simp
      have hp_sq_dvd_2p : p ^ 2 ∣ 2 * p := by
        have h_natCast : (2 * (p : ZMod (p ^ 2))) = ((2 * p : ℕ) : ZMod (p ^ 2)) := by simp
        rw [h_natCast] at h_2p_zero
        apply (ZMod.natCast_eq_zero_iff (2 * p) (p ^ 2)).mp
        exact h_2p_zero
      have hp_le_2 : p ≤ 2 := by
        have hp_pos : 0 < p := hp.pos
        have hp_sq_le_2p : p ^ 2 ≤ 2 * p :=
          Nat.le_of_dvd (by omega) hp_sq_dvd_2p
        have h_mul : p * p ≤ 2 * p := by
          simpa [sq] using hp_sq_le_2p
        exact Nat.le_of_mul_le_mul_right h_mul hp_pos
      have h2_le_p : 2 ≤ p := hp.two_le
      have hp_eq_2 : p = 2 := by omega
      exfalso
      exact hp2 hp_eq_2

/-! ### Auxiliary lemmas about `CyclicRep (p²)` -/

private lemma pow_gen {p n : ℕ} (m : ℕ) :
    ((Multiplicative.ofAdd 1 : CyclicRep (p ^ n)) ^ m)
    = Multiplicative.ofAdd (m : ZMod (p ^ n)) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih]; simp

private lemma cyclicRep_pow_gen {p n : ℕ} [NeZero (p ^ n)] (x : CyclicRep (p ^ n)) :
    x = ((Multiplicative.ofAdd 1 : CyclicRep (p ^ n)) ^ (Multiplicative.toAdd x).val) := by
  let v := (Multiplicative.toAdd x).val
  calc
    x = Multiplicative.ofAdd (Multiplicative.toAdd x) := rfl
    _ = Multiplicative.ofAdd ((v : ZMod (p ^ n))) := by
      rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd x)]
    _ = ((Multiplicative.ofAdd 1 : CyclicRep (p ^ n)) ^ v) := by
      rw [← pow_gen v]

/-! ### Involutions in `MulAut (CyclicRep (p²))` are `±1` -/

theorem cyclicRep_mulAut_involution {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (CyclicRep (p ^ 2))) (hα : α ^ 2 = 1) :
    α = 1 ∨ α = invAut (CyclicRep (p ^ 2)) := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let g : CyclicRep (p ^ 2) := Multiplicative.ofAdd 1
  let k := (Multiplicative.toAdd (α g)).val
  have hαg : α g = g ^ k := by rw [cyclicRep_pow_gen (α g)]
  have h_sq_eq : (α ^ 2) g = g := by rw [hα, MulAut.one_apply]
  have h_pow_sq : (α ^ 2) g = g ^ (k * k) := by
    calc
      (α ^ 2) g = α (α g) := by simp [sq]
      _ = α (g ^ k) := by rw [hαg]
      _ = (α g) ^ k := map_pow _ _ _
      _ = (g ^ k) ^ k := by rw [hαg]
      _ = g ^ (k * k) := by rw [← pow_mul, mul_comm]
  rw [h_pow_sq] at h_sq_eq
  rw [pow_gen (k * k), ← pow_one g, pow_gen 1] at h_sq_eq
  have h_sq_mod : ((k : ℕ) : ZMod (p ^ 2)) ^ 2 = 1 := by
    have := congrArg Multiplicative.toAdd h_sq_eq
    simpa [Nat.cast_mul, sq] using this
  rcases square_eq_one_zmod_psq hp hp2 (k : ZMod (p ^ 2)) h_sq_mod with (hk | hk)
  · have hαg_one : α g = g := by
      rw [hαg, pow_gen, hk]
    left
    ext x
    have hx : x = g ^ (Multiplicative.toAdd x).val := cyclicRep_pow_gen x
    rw [hx]
    simp [hαg_one]
  · have hαg_inv : α g = invAut (CyclicRep (p ^ 2)) g := by
      rw [hαg, invAut_apply, pow_gen, hk]
      dsimp [g]
    right
    ext x
    have hx : x = g ^ (Multiplicative.toAdd x).val := cyclicRep_pow_gen x
    rw [hx]
    simp [hαg_inv]

/-! ### Isomorphism `ℤ/p² ⋊[trivial] ℤ/2 ≅ R1 = ℤ/2p²` via CRT -/

noncomputable def cyclicCase_trivial_iso {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    CyclicRep (p ^ 2) × Multiplicative (ZMod 2) ≃* R1 p := by
  have hp : p.Prime := Fact.out
  have hcop : (p ^ 2).Coprime 2 :=
    Nat.Coprime.pow_left 2 (hp.coprime_iff_not_dvd.mpr fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
  let e_crt : ZMod ((p ^ 2) * 2) ≃+* ZMod (p ^ 2) × ZMod 2 := ZMod.chineseRemainder hcop
  let e_add : Multiplicative (ZMod ((p ^ 2) * 2)) ≃* Multiplicative (ZMod (p ^ 2) × ZMod 2) :=
    AddEquiv.toMultiplicative e_crt.toAddEquiv
  let e_prod : Multiplicative (ZMod (p ^ 2) × ZMod 2) ≃*
      Multiplicative (ZMod (p ^ 2)) × Multiplicative (ZMod 2) :=
    MulEquiv.prodMultiplicative (ZMod (p ^ 2)) (ZMod 2)
  let e_mul : R1 p ≃* Multiplicative (ZMod ((p ^ 2) * 2)) := by
    refine AddEquiv.toMultiplicative (ZMod.ringEquivCongr ?_).toAddEquiv
    rw [mul_comm]
  exact (e_mul.trans (e_add.trans e_prod)).symm

theorem cyclicCase_trivial_action {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Nonempty (CyclicRep (p ^ 2) ⋊[(1 : Multiplicative (ZMod 2) →* MulAut (CyclicRep (p ^ 2)))]
      Multiplicative (ZMod 2) ≃* R1 p) := by
  let e : CyclicRep (p ^ 2) ⋊[(1 : Multiplicative (ZMod 2) →* MulAut (CyclicRep (p ^ 2)))]
      Multiplicative (ZMod 2) ≃* CyclicRep (p ^ 2) × Multiplicative (ZMod 2) :=
    { toEquiv := SemidirectProduct.equivProd
      map_mul' := fun x y => by
        rcases x with ⟨n₁, h₁⟩
        rcases y with ⟨n₂, h₂⟩
        simp }
  exact ⟨e.trans (cyclicCase_trivial_iso hp2)⟩

/-! ### Isomorphism `ℤ/p² ⋊[inversion] ℤ/2 ≅ R3 = D_{p²}` -/

private lemma multiplicative_zmod_two_cases (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  fin_cases x <;> decide

noncomputable def cyclicCase_inv_iso {p : ℕ} [Fact p.Prime] (_ : p ≠ 2) :
    CyclicRep (p ^ 2) ⋊[invActionHom (CyclicRep (p ^ 2))] Multiplicative (ZMod 2) ≃* R3 p := by
  have hp : p.Prime := Fact.out
  let fn : CyclicRep (p ^ 2) →* DihedralGroup (p ^ 2) :=
    { toFun := fun x => DihedralGroup.r (Multiplicative.toAdd x)
      map_one' := by simp
      map_mul' x y := by
        simp [DihedralGroup.r_mul_r, toAdd_mul] }
  let fg : Multiplicative (ZMod 2) →* DihedralGroup (p ^ 2) :=
    { toFun := fun x => if x = 1 then 1 else DihedralGroup.sr 0
      map_one' := by simp
      map_mul' a b := by
        rcases multiplicative_zmod_two_cases a with rfl | rfl
        · simp
        · rcases multiplicative_zmod_two_cases b with rfl | rfl
          · simp
          · have h_prod : Multiplicative.ofAdd (1 : ZMod 2) *
              Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide
            simp [h_prod] }
  have hcompat : ∀ g : Multiplicative (ZMod 2),
      fn.comp ((invActionHom (CyclicRep (p ^ 2))) g).toMonoidHom =
        (MulAut.conj (fg g)).toMonoidHom.comp fn := by
    intro g
    rcases multiplicative_zmod_two_cases g with rfl | rfl
    · ext x; simp [fn, fg]
    · ext x
      simp [fn, fg, invActionHom_gen, invAut_apply,
        DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr,
        DihedralGroup.inv_sr]
  let f := SemidirectProduct.lift fn fg hcompat
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rcases x with ⟨n, g⟩
    have hfn_fg : fn n * fg g = 1 := hx
    rcases multiplicative_zmod_two_cases g with rfl | rfl
    · simp only [fn, fg] at hfn_fg
      have h_add_zero : Multiplicative.toAdd n = (0 : ZMod (p ^ 2)) := by
        have hr_eq : DihedralGroup.r (Multiplicative.toAdd n)
        = DihedralGroup.r (0 : ZMod (p ^ 2)) := by
          simpa [DihedralGroup.r_zero] using hfn_fg
        exact DihedralGroup.r.inj hr_eq
      have hn : n = 1 := Multiplicative.toAdd.injective (by simpa using h_add_zero)
      simp [hn]
    · have hcalc : fn n * fg (Multiplicative.ofAdd 1) =
          DihedralGroup.sr (-Multiplicative.toAdd n) := by
        simp [fn, fg, DihedralGroup.r_mul_sr]
      rw [hcalc] at hfn_fg
      have : DihedralGroup.sr (-Multiplicative.toAdd n) ≠ (1 : DihedralGroup (p ^ 2)) := by
        intro h_eq; cases h_eq
      exact absurd hfn_fg this
  haveI : Finite (CyclicRep (p ^ 2) ⋊[invActionHom (CyclicRep (p ^ 2))]
      Multiplicative (ZMod 2)) :=
    Finite.of_equiv (CyclicRep (p ^ 2) × Multiplicative (ZMod 2))
      SemidirectProduct.equivProd.symm
  haveI : Fintype (CyclicRep (p ^ 2) ⋊[invActionHom (CyclicRep (p ^ 2))]
      Multiplicative (ZMod 2)) :=
    Fintype.ofFinite _
  haveI : Fintype (DihedralGroup (p ^ 2)) := by
    haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
    exact inferInstance
  have hcard_nat : Nat.card (CyclicRep (p ^ 2) ⋊[invActionHom (CyclicRep (p ^ 2))]
      Multiplicative (ZMod 2)) = Nat.card (DihedralGroup (p ^ 2)) := by
    calc
      Nat.card (CyclicRep (p ^ 2) ⋊[invActionHom (CyclicRep (p ^ 2))] Multiplicative (ZMod 2))
          = Nat.card (CyclicRep (p ^ 2)) * Nat.card (Multiplicative (ZMod 2)) := by
        rw [SemidirectProduct.card]
      _ = (p ^ 2) * 2 := by
        rw [card_cyclicRep (pow_ne_zero 2 hp.ne_zero),
          Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      _ = 2 * p ^ 2 := by ring
      _ = Nat.card (DihedralGroup (p ^ 2)) := by rw [DihedralGroup.nat_card]
  have hcard_fintype : Fintype.card (CyclicRep (p ^ 2) ⋊[invActionHom (CyclicRep (p ^ 2))]
      Multiplicative (ZMod 2)) = Fintype.card (DihedralGroup (p ^ 2)) := by
    simpa [Nat.card_eq_fintype_card] using hcard_nat
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard_fintype⟩
  exact MulEquiv.ofBijective f hbij

theorem cyclicCase_inv_action {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Nonempty (CyclicRep (p ^ 2) ⋊[invActionHom (CyclicRep (p ^ 2))]
      Multiplicative (ZMod 2) ≃* R3 p) :=
  ⟨cyclicCase_inv_iso hp2⟩

/-! ### Main theorem: cyclic Sylow case → R1 or R3 -/

theorem order2psq_cyclicCase {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (φ : Multiplicative (ZMod 2) →* MulAut (CyclicRep (p ^ 2)))
    (hG : Nonempty (G ≃* SemidirectProduct (CyclicRep (p ^ 2)) (Multiplicative (ZMod 2)) φ)) :
    Nonempty (G ≃* R1 p) ∨ Nonempty (G ≃* R3 p) := by
  have hp : p.Prime := Fact.out
  obtain ⟨e⟩ := hG
  let α := φ (Multiplicative.ofAdd 1)
  have hα2 : α ^ 2 = 1 := by
    have h_order_two : Multiplicative.ofAdd (1 : ZMod 2) ^ 2 = 1 := by
      decide
    calc
      α ^ 2 = (φ (Multiplicative.ofAdd 1)) ^ 2 := rfl
      _ = φ ((Multiplicative.ofAdd 1) ^ 2) := by rw [map_pow]
      _ = φ 1 := by rw [h_order_two]
      _ = 1 := map_one _
  rcases cyclicRep_mulAut_involution hp hp2 α hα2 with (hα | hα)
  · have hφ_triv : φ = 1 :=
      MonoidHom.ext fun g => MulEquiv.ext fun x => by
        rcases multiplicative_zmod_two_cases g with rfl | rfl
        · simp
        · dsimp [α] at hα; rw [hα]; rfl
    subst hφ_triv
    left; exact ⟨e.trans (cyclicCase_trivial_action hp2).some⟩
  · have hφ_inv : φ = invActionHom (CyclicRep (p ^ 2)) :=
      MonoidHom.ext fun g => MulEquiv.ext fun x => by
        rcases multiplicative_zmod_two_cases g with rfl | rfl
        · simp
        · dsimp [α] at hα; rw [hα, invActionHom_gen]
    subst hφ_inv
    right; exact ⟨e.trans (cyclicCase_inv_action hp2).some⟩

end Smallgroups.UsefulTheorems
