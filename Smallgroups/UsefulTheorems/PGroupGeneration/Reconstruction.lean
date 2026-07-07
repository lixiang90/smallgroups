/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleGroup

/-!
# p-group generation: every central extension is a cocycle group

The converse to `PGroupGeneration/CocycleGroup.lean`: if `π : G →* Q` is surjective with
kernel the cyclic central subgroup `⟨z⟩` of order `n`, then `G` is isomorphic to
`CocycleGroup f hf` for some normalized 2-cocycle `f : Q → Q → ZMod n`
(`cocycleGroup_reconstruction`).

The proof is the classical one: choose a set-theoretic section `s : Q → G` of `π` with
`s 1 = 1`; the defect `s q₁ * s q₂ * (s (q₁ q₂))⁻¹` lies in `ker π = ⟨z⟩`, so writing it
as `z ^ f q₁ q₂` defines the cocycle, and `(m, q) ↦ z ^ m * s q` is the isomorphism
(multiplicativity is exactly the cocycle bookkeeping, using that `z` is central).

Combined with `order_prime_pow_central_reduction` (`CentralExtension.lean`) and the known
classification one order below, `cocycleGroup_reconstruction_of_quotient_iso` reduces the
classification of groups of order `p ^ (n + 1)` to the analysis of cocycles valued in
`ZMod p` over each known group of order `p ^ n`.

The discrete-exponential `zmodZPowHom n z hzn : Multiplicative (ZMod n) →* G`,
`k ↦ z ^ k`, is also provided here with its injectivity criterion.
-/

namespace Smallgroups.UsefulTheorems

variable {G : Type*} [Group G] {Q : Type*} [Group Q]

/-- The "discrete exponential" `Multiplicative (ZMod n) →* G`, `k ↦ g ^ k`, defined for any
`g` with `g ^ n = 1`. -/
noncomputable def zmodZPowHom (n : ℕ) (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  AddMonoidHom.toMultiplicativeLeft <| ZMod.lift n
    ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
      rw [zmultiplesHom_apply, ← ofMul_zpow, zpow_natCast, hg, ofMul_one]⟩

theorem zmodZPowHom_intCast (n : ℕ) (g : G) (hg : g ^ n = 1) (k : ℤ) :
    zmodZPowHom n g hg (Multiplicative.ofAdd ((k : ZMod n))) = g ^ k := by
  simp only [zmodZPowHom, AddMonoidHom.toMultiplicativeLeft_apply_apply, toAdd_ofAdd]
  rw [ZMod.lift_coe, zmultiplesHom_apply, ← ofMul_zpow, toMul_ofMul]

theorem zmodZPowHom_mem_zpowers (n : ℕ) (g : G) (hg : g ^ n = 1)
    (m : Multiplicative (ZMod n)) : zmodZPowHom n g hg m ∈ Subgroup.zpowers g := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := n) m.toAdd
  have hm : Multiplicative.ofAdd ((k : ZMod n)) = m :=
    (congrArg Multiplicative.ofAdd hk).trans (ofAdd_toAdd m)
  rw [← hm, zmodZPowHom_intCast]
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩

/-- If `g` has order exactly `n`, the discrete exponential is injective. -/
theorem zmodZPowHom_injective (n : ℕ) [NeZero n] (g : G) (hg : g ^ n = 1)
    (hord : orderOf g = n) : Function.Injective (zmodZPowHom n g hg) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := n) a.toAdd
  have hm : Multiplicative.ofAdd ((k : ZMod n)) = a :=
    (congrArg Multiplicative.ofAdd hk).trans (ofAdd_toAdd a)
  rw [← hm, zmodZPowHom_intCast] at ha
  have hdvd : ((n : ℤ)) ∣ k := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr ha
  have hk0 : ((k : ZMod n)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd k n).mpr hdvd
  rw [← hm, hk0]
  rfl

/-- **Reconstruction**: if `π : G →* Q` is surjective with kernel the central cyclic
subgroup `⟨z⟩` of order `n`, then `G` is a cocycle group over `Q` with values in
`ZMod n`. -/
theorem cocycleGroup_reconstruction {n : ℕ} [NeZero n] (π : G →* Q)
    (hπ : Function.Surjective π) {z : G} (hz : z ∈ Subgroup.center G)
    (hord : orderOf z = n) (hker : π.ker = Subgroup.zpowers z) :
    ∃ (f : Q → Q → ZMod n) (hf : IsCentralCocycle f),
      Nonempty (G ≃* CocycleGroup f hf) := by
  classical
  have hzn : z ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one z
  have hζinj : Function.Injective (zmodZPowHom n z hzn) :=
    zmodZPowHom_injective n z hzn hord
  have hcen : ∀ (m : Multiplicative (ZMod n)) (h : G),
      h * zmodZPowHom n z hzn m = zmodZPowHom n z hzn m * h := fun m h =>
    Subgroup.mem_center_iff.mp
      (Subgroup.zpowers_le.mpr hz (zmodZPowHom_mem_zpowers n z hzn m)) h
  have hval : ∀ x : ZMod n, zmodZPowHom n z hzn (Multiplicative.ofAdd x) = 1 → x = 0 := by
    intro x hx
    have h1 : Multiplicative.ofAdd x = 1 := hζinj (by rw [hx, map_one])
    simpa using h1
  -- a set-theoretic section of `π`, normalized at `1`
  let s : Q → G := fun q => if q = 1 then 1 else Function.surjInv hπ q
  have hs1 : s 1 = 1 := if_pos rfl
  have hπs : ∀ q, π (s q) = q := by
    intro q
    by_cases h : q = 1
    · rw [h, hs1, map_one]
    · change π (if q = 1 then 1 else Function.surjInv hπ q) = q
      rw [if_neg h]
      exact Function.surjInv_eq hπ q
  -- the defect of the section lies in `ker π = ⟨z⟩`
  have hdef : ∀ q₁ q₂ : Q, ∃ k : ℤ, z ^ k = s q₁ * s q₂ * (s (q₁ * q₂))⁻¹ := by
    intro q₁ q₂
    have hmem : s q₁ * s q₂ * (s (q₁ * q₂))⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hπs, hπs, hπs, mul_inv_cancel]
    rw [hker] at hmem
    exact Subgroup.mem_zpowers_iff.mp hmem
  -- the cocycle
  let f : Q → Q → ZMod n := fun q₁ q₂ => ((Classical.choose (hdef q₁ q₂) : ℤ) : ZMod n)
  have key : ∀ q₁ q₂ : Q, s q₁ * s q₂
      = zmodZPowHom n z hzn (Multiplicative.ofAdd (f q₁ q₂)) * s (q₁ * q₂) := by
    intro q₁ q₂
    change s q₁ * s q₂ = zmodZPowHom n z hzn
      (Multiplicative.ofAdd ((Classical.choose (hdef q₁ q₂) : ℤ) : ZMod n)) * s (q₁ * q₂)
    rw [zmodZPowHom_intCast, Classical.choose_spec (hdef q₁ q₂), inv_mul_cancel_right]
  have hf : IsCentralCocycle f := by
    constructor
    · intro a b c
      have h1 : s a * s b * s c = zmodZPowHom n z hzn
          (Multiplicative.ofAdd (f a b + f (a * b) c)) * s (a * b * c) := by
        rw [key a b, mul_assoc, key (a * b) c, ← mul_assoc, ← map_mul, ← ofAdd_add]
      have h2 : s a * (s b * s c) = zmodZPowHom n z hzn
          (Multiplicative.ofAdd (f b c + f a (b * c))) * s (a * (b * c)) := by
        rw [key b c, ← mul_assoc, hcen _ (s a), mul_assoc, key a (b * c), ← mul_assoc,
          ← map_mul, ← ofAdd_add]
      rw [mul_assoc a b c] at h1
      have h4 := mul_right_cancel
        ((h1.symm.trans (mul_assoc (s a) (s b) (s c))).trans h2)
      exact Multiplicative.ofAdd.injective (hζinj h4)
    · intro a
      have h := key 1 a
      rw [hs1, one_mul, one_mul] at h
      exact hval _ (mul_right_cancel ((one_mul (s a)).trans h)).symm
    · intro a
      have h := key a 1
      rw [hs1, mul_one, mul_one] at h
      exact hval _ (mul_right_cancel ((one_mul (s a)).trans h)).symm
  refine ⟨f, hf, ⟨(MulEquiv.ofBijective (MonoidHom.mk'
    (fun x : CocycleGroup f hf => zmodZPowHom n z hzn (Multiplicative.ofAdd x.fst) * s x.snd)
    ?_) ⟨?_, ?_⟩).symm⟩⟩
  -- multiplicativity: exactly the cocycle bookkeeping
  · intro x y
    simp only [CocycleGroup.mul_fst, CocycleGroup.mul_snd, ofAdd_add, map_mul]
    rw [mul_assoc, ← key]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, ← hcen _ (s x.snd), mul_assoc]
  -- injectivity
  · rw [injective_iff_map_eq_one]
    intro x hx
    simp only [MonoidHom.mk'_apply] at hx
    have hq : x.snd = 1 := by
      have h1 : π (zmodZPowHom n z hzn (Multiplicative.ofAdd x.fst)) = 1 :=
        MonoidHom.mem_ker.mp
          (hker ▸ zmodZPowHom_mem_zpowers n z hzn (Multiplicative.ofAdd x.fst))
      have h2 := congrArg π hx
      rw [map_mul, h1, one_mul, map_one, hπs] at h2
      exact h2
    have hz1 : zmodZPowHom n z hzn (Multiplicative.ofAdd x.fst) = 1 := by
      rw [hq, hs1, mul_one] at hx
      exact hx
    ext
    · exact hval _ hz1
    · exact hq
  -- surjectivity
  · intro g
    obtain ⟨k, hk⟩ : ∃ k : ℤ, z ^ k = g * (s (π g))⁻¹ := by
      have hmem : g * (s (π g))⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπs, mul_inv_cancel]
      rw [hker] at hmem
      exact Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨⟨((k : ZMod n)), π g⟩, ?_⟩
    simp only [MonoidHom.mk'_apply]
    rw [zmodZPowHom_intCast, hk, inv_mul_cancel_right]

/-- Reconstruction over a **concrete model** of the quotient: if `z` is central of order
`n` and `G ⧸ ⟨z⟩ ≃* R`, then `G` is a cocycle group over `R`.  This is the form used to
classify order `p ^ (m + 1)`: `R` ranges over the known representatives of order
`p ^ m`. -/
theorem cocycleGroup_reconstruction_of_quotient_iso {R : Type*} [Group R] {z : G}
    (hz : z ∈ Subgroup.center G) {n : ℕ} [NeZero n] (hord : orderOf z = n)
    [hnorm : (Subgroup.zpowers z).Normal]
    (e : (G ⧸ Subgroup.zpowers z) ≃* R) :
    ∃ (f : R → R → ZMod n) (hf : IsCentralCocycle f),
      Nonempty (G ≃* CocycleGroup f hf) := by
  refine cocycleGroup_reconstruction (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hz hord ?_
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  rw [show e.toMonoidHom (QuotientGroup.mk' (Subgroup.zpowers z) x)
      = e (QuotientGroup.mk' (Subgroup.zpowers z) x) from rfl]
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end Smallgroups.UsefulTheorems
