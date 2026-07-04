/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order80.Sylow
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Smallgroups.UsefulTheorems.Order16_Wild
import Smallgroups.UsefulTheorems.Order40
import Smallgroups.UsefulTheorems.Order60.Classification

/-!
# Groups of order 80 with a unique Sylow-5 subgroup

This file handles the first branch of `order80_sylow_dichotomy`
(`Order80/Sylow.lean`): if a group `G` of order `80` has `n₅ = 1`, its unique
Sylow `5`-subgroup `N` is normal, and since `Nat.Coprime 5 16` the
Schur–Zassenhaus theorem splits `G` as a semidirect product `N ⋊[φ] K` with
`Nat.card N = 5` and `Nat.card K = 16`.

* `order80_semidirectProduct_of_sylow_five_normal`: the reduction.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-- **Semidirect-product reduction for order `80` with a unique Sylow-`5`
subgroup.** If `G` has order `80` and its Sylow `5`-subgroup is normal, then
`G` is a semidirect product `N ⋊[φ] K`, where `N` has order `5` and `K` has
order `16`. -/
theorem order80_semidirectProduct_of_sylow_five_normal [Finite G] (hG : Nat.card G = 80)
    (hSyl : Nat.card (Sylow 5 G) = 1) :
    ∃ (N K : Subgroup G) (φ : K →* MulAut N),
      N.Normal ∧ Nat.card N = 5 ∧ Nat.card K = 16 ∧
        Nonempty (G ≃* SemidirectProduct N K φ) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 5 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := sylow_five_normal_of_card_sylow_five_eq_one hSyl P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 5 := card_sylow_five_subgroup_of_card_80 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have := P0.not_dvd_index
    exact (show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr this
  obtain ⟨K, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardK : Nat.card K = 16 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card K := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 5 * Nat.card K = 5 * 16 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5) h1'
  exact ⟨↑P0, K, φ, hnorm, hcardN, hcardK, ⟨e⟩⟩

/-! ### Classifying the action on the order-`16` complement

Since `N` has order `5`, `Aut N ≅ (ZMod 5)ˣ` via `unitAutHom`, so every action
`φ : K →* MulAut N` factors as `unitAutHom.comp ψ` for a unique character
`ψ : K →* (ZMod 5)ˣ` (`exists_unitAutHom_comp_eq`).  Since `(ZMod 5)ˣ` is
abelian, `ψ` is determined by its restriction to the two pieces of `K` when
`K` is built as a direct or semidirect product, via
`SemidirectProduct.hom_ext`/`SemidirectProduct.lift`.  This section develops
that reduction for each of the fourteen isomorphism types of `K`
(`order16_wild_reps`, from `Order16_Wild.lean`). -/

/-- A homomorphism out of a semidirect product with commutative codomain is invariant, when
composed with `inl`, under the defining action `φ`. -/
theorem hom_semidirectProduct_inl_invariant {A B M : Type*} [Group A] [Group B] [CommGroup M]
    {φ : B →* MulAut A} (ψ : SemidirectProduct A B φ →* M) (b : B) (a : A) :
    ψ (SemidirectProduct.inl (φ b a)) = ψ (SemidirectProduct.inl a) := by
  rw [SemidirectProduct.inl_aut, map_mul, map_mul, map_inv, map_inv,
    mul_comm (ψ (SemidirectProduct.inr b)) (ψ (SemidirectProduct.inl a))]
  group

/-- Any homomorphism out of a semidirect product with commutative codomain is the `lift` of its
restrictions to `inl` and `inr`. -/
theorem eq_lift_of_semidirectProduct_hom {A B M : Type*} [Group A] [Group B] [CommGroup M]
    {φ : B →* MulAut A} (ψ : SemidirectProduct A B φ →* M) :
    ψ = SemidirectProduct.lift (ψ.comp SemidirectProduct.inl) (ψ.comp SemidirectProduct.inr)
      (fun b => by
        ext a
        simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
        rw [mul_comm (ψ (SemidirectProduct.inr b)) (ψ (SemidirectProduct.inl a)),
          mul_inv_cancel_right]
        exact hom_semidirectProduct_inl_invariant ψ b a) :=
  SemidirectProduct.lift_unique ψ

/-- `unitAut n u` sends the generator of `Multiplicative (ZMod n)` to that generator raised to
the power `u.val`. -/
theorem unitAut_ofAdd_one (n : ℕ) [NeZero n] (u : (ZMod n)ˣ) :
    unitAut n u (Multiplicative.ofAdd (1 : ZMod n)) =
      (Multiplicative.ofAdd (1 : ZMod n)) ^ (u : ZMod n).val := by
  change Multiplicative.ofAdd ((u : ZMod n) • (1 : ZMod n)) = _
  rw [smul_eq_mul, mul_one, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

/-- The automorphism `φ₂ : x ↦ x³` of `C₈`, on the generator. -/
theorem phi2_gen : phi2 (Multiplicative.ofAdd (1 : ZMod 8)) =
    (Multiplicative.ofAdd (1 : ZMod 8)) ^ 3 := by
  rw [phi2, unitAut_ofAdd_one]; congr 1

/-- The automorphism `φ₃ : x ↦ x⁵` of `C₈`, on the generator. -/
theorem phi3_gen : phi3 (Multiplicative.ofAdd (1 : ZMod 8)) =
    (Multiplicative.ofAdd (1 : ZMod 8)) ^ 5 := by
  rw [phi3, unitAut_ofAdd_one]; congr 1

/-- The automorphism `φ₄ : x ↦ x⁷` of `C₈`, on the generator. -/
theorem phi4_gen : phi4 (Multiplicative.ofAdd (1 : ZMod 8)) =
    (Multiplicative.ofAdd (1 : ZMod 8)) ^ 7 := by
  rw [phi4, unitAut_ofAdd_one]; congr 1

/-- Homomorphisms out of `Multiplicative (ZMod 2)` are determined by the generator. -/
theorem c2_hom_ext {M : Type*} [Monoid M] {χ ψ : Multiplicative (ZMod 2) →* M}
    (h : χ (Multiplicative.ofAdd (1 : ZMod 2)) = ψ (Multiplicative.ofAdd (1 : ZMod 2))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  have hx : x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) := by revert x; decide
  rcases hx with rfl | rfl
  · simp
  · exact h

/-- Characters `Multiplicative (ZMod 2) → (ZMod 5)ˣ` are trivial or `order40_c2UnitHom`. -/
theorem c2_unit_character_cases (χ : Multiplicative (ZMod 2) →* (ZMod 5)ˣ) :
    χ = 1 ∨ χ = order40_c2UnitHom := by
  have hsq : χ (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by
    rw [← map_pow]
    have : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by decide
    rw [this, map_one]
  rcases order40_unit_sq_eq_one_cases _ hsq with h | h
  · exact Or.inl (c2_hom_ext (by simp [h]))
  · exact Or.inr (c2_hom_ext (by rw [h, order40_c2UnitHom_gen]))

/-! ### The `C₈`-extension family (`G₂ = SD₁₆`, `G₃ = M₁₆`, `G₄ = D₁₆`) -/

theorem c2Action_phi2_gen : c2Action_phi2 (Multiplicative.ofAdd (1 : ZMod 2)) = phi2 := by
  change (if (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 then 1 else phi2) =
    phi2
  rw [if_neg (by decide)]

theorem c2Action_phi3_gen : c2Action_phi3 (Multiplicative.ofAdd (1 : ZMod 2)) = phi3 := by
  change (if (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 then 1 else phi3) =
    phi3
  rw [if_neg (by decide)]

theorem c2Action_phi4_gen : c2Action_phi4 (Multiplicative.ofAdd (1 : ZMod 2)) = phi4 := by
  change (if (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 then 1 else phi4) =
    phi4
  rw [if_neg (by decide)]

/-- **Exhaustiveness for `K = SD₁₆` (`G₂`, action `φ₂ : x ↦ x³`).**  The character on the
`C₈`-part must square to `1`. -/
theorem order80_classify_G2 (φ' : order16_wild_G2 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : order16_wild_G2 →* (ZMod 5)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨ χ.comp SemidirectProduct.inl = order40_chiC8_two) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  refine ⟨ψ, ?_, ⟨semidirectProductCongr_eq hψ⟩⟩
  set χA := ψ.comp SemidirectProduct.inl with hχA
  set g : C8g := Multiplicative.ofAdd (1 : ZMod 8) with hg
  set s : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2) with hs
  have hkey : χA g ^ 3 = χA g := by
    have h1 := hom_semidirectProduct_inl_invariant ψ s g
    rw [show c2Action_phi2 s g = phi2 g from by rw [c2Action_phi2_gen], phi2_gen,
      map_pow, map_pow] at h1
    exact h1
  have hsq : χA g ^ 2 = 1 := by
    have := congrArg (· * (χA g)⁻¹) hkey
    simpa [pow_succ, mul_assoc] using this
  rcases order40_c8_unit_character_cases χA with h | h | h | h
  · exact Or.inl h
  · exfalso
    rw [h, order40_chiC8_four_gen] at hsq
    exact absurd hsq (by decide)
  · exact Or.inr h
  · exfalso
    rw [h, order40_chiC8_four_inv_gen] at hsq
    exact absurd hsq (by decide)

/-- **Exhaustiveness for `K = M₁₆` (`G₃`, action `φ₃ : x ↦ x⁵`).**  No constraint arises: all
four characters on the `C₈`-part occur. -/
theorem order80_classify_G3 (φ' : order16_wild_G3 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : order16_wild_G3 →* (ZMod 5)ˣ,
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, ⟨semidirectProductCongr_eq hψ⟩⟩

/-- **Exhaustiveness for `K = D₁₆` (`G₄`, action `φ₄ : x ↦ x⁷`, inversion).**  The character on
the `C₈`-part must square to `1`. -/
theorem order80_classify_G4 (φ' : order16_wild_G4 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : order16_wild_G4 →* (ZMod 5)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨ χ.comp SemidirectProduct.inl = order40_chiC8_two) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4 (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  refine ⟨ψ, ?_, ⟨semidirectProductCongr_eq hψ⟩⟩
  set χA := ψ.comp SemidirectProduct.inl with hχA
  set g : C8g := Multiplicative.ofAdd (1 : ZMod 8) with hg
  set s : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2) with hs
  have hkey : χA g ^ 7 = χA g := by
    have h1 := hom_semidirectProduct_inl_invariant ψ s g
    rw [show c2Action_phi4 s g = phi4 g from by rw [c2Action_phi4_gen], phi4_gen,
      map_pow, map_pow] at h1
    exact h1
  rcases order40_c8_unit_character_cases χA with h | h | h | h
  · exact Or.inl h
  · exfalso
    rw [h, order40_chiC8_four_gen] at hkey
    exact absurd hkey (by decide)
  · exact Or.inr h
  · exfalso
    rw [h, order40_chiC8_four_inv_gen] at hkey
    exact absurd hkey (by decide)

/-! ### The `K₈`-extension family (`G₈ = D₈×C₂`, `G₉`, `G₁₀ = Q₈⋊C₂`) -/

theorem c2Action_psi3_gen : c2Action_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) = psi3 := by
  change (if (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 then 1 else psi3) =
    psi3
  rw [if_neg (by decide)]

theorem c2Action_psi5_gen : c2Action_psi5 (Multiplicative.ofAdd (1 : ZMod 2)) = psi5 := by
  change (if (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 then 1 else psi5) =
    psi5
  rw [if_neg (by decide)]

theorem c2Action_psi6_gen : c2Action_psi6 (Multiplicative.ofAdd (1 : ZMod 2)) = psi6 := by
  change (if (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 then 1 else psi6) =
    psi6
  rw [if_neg (by decide)]

/-- The two standard generators of `K₈ = C₄ × C₂`. -/
abbrev k8g4 : K8g := (Multiplicative.ofAdd (1 : ZMod 4), 1)
abbrev k8g2 : K8g := (1, Multiplicative.ofAdd (1 : ZMod 2))

theorem psi3_g4 : psi3 k8g4 = k8g4⁻¹ := by decide
theorem psi5_g4 : psi5 k8g4 = k8g4 * k8g2 := by decide
theorem psi5_g2 : psi5 k8g2 = k8g2 := by decide
theorem psi6_g4 : psi6 k8g4 = k8g4⁻¹ := by decide

/-- **Exhaustiveness for `K = D₈ × C₂` (`G₈`, action `ψ₃ : (x,y) ↦ (x⁻¹,y)`).**  The
character on the `C₄`-generator must square to `1`. -/
theorem order80_classify_G8 (φ' : order16_wild_G8 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : order16_wild_G8 →* (ZMod 5)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨
        χ.comp SemidirectProduct.inl = order40_chiC4C2_fst_two ∨
        χ.comp SemidirectProduct.inl = order40_chiC4C2_snd_two ∨
        χ.comp SemidirectProduct.inl = order40_chiC4C2_prod_two) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  refine ⟨ψ, ?_, ⟨semidirectProductCongr_eq hψ⟩⟩
  have hkey : (ψ.comp SemidirectProduct.inl) k8g4 ^ 2 = 1 := by
    have h1 := hom_semidirectProduct_inl_invariant ψ
      (Multiplicative.ofAdd (1 : ZMod 2)) k8g4
    rw [show c2Action_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) k8g4 = psi3 k8g4 from
      by rw [c2Action_psi3_gen], psi3_g4, map_inv, map_inv] at h1
    change ψ (SemidirectProduct.inl k8g4) ^ 2 = 1
    rw [sq]
    calc ψ (SemidirectProduct.inl k8g4) * ψ (SemidirectProduct.inl k8g4)
        = (ψ (SemidirectProduct.inl k8g4))⁻¹ * ψ (SemidirectProduct.inl k8g4) := by rw [h1]
      _ = 1 := inv_mul_cancel _
  rcases order40_c4c2_unit_character_cases (ψ.comp SemidirectProduct.inl) with
    h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exfalso; rw [h, order40_chiC4C2_fst_four_g4] at hkey; exact absurd hkey (by decide)
  · exfalso; rw [h, order40_chiC4C2_fst_four_snd_g4] at hkey; exact absurd hkey (by decide)
  · exfalso; rw [h, order40_chiC4C2_fst_four_inv_g4] at hkey; exact absurd hkey (by decide)
  · exfalso; rw [h, order40_chiC4C2_fst_four_inv_snd_g4] at hkey; exact absurd hkey (by decide)

/-- **Exhaustiveness for `K = "K₄⋊C₄"` (`G₉`, action `ψ₅ : (x,y) ↦ (x,c(x)y)`).**  The
character on the `C₂`-generator must vanish. -/
theorem order80_classify_G9 (φ' : order16_wild_G9 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : order16_wild_G9 →* (ZMod 5)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨
        χ.comp SemidirectProduct.inl = order40_chiC4C2_fst_two ∨
        χ.comp SemidirectProduct.inl = order40_chiC4C2_fst_four ∨
        χ.comp SemidirectProduct.inl = order40_chiC4C2_fst_four_inv) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  refine ⟨ψ, ?_, ⟨semidirectProductCongr_eq hψ⟩⟩
  have hkey : (ψ.comp SemidirectProduct.inl) k8g2 = 1 := by
    have h1 := hom_semidirectProduct_inl_invariant ψ
      (Multiplicative.ofAdd (1 : ZMod 2)) k8g4
    rw [show c2Action_psi5 (Multiplicative.ofAdd (1 : ZMod 2)) k8g4 = psi5 k8g4 from
      by rw [c2Action_psi5_gen], psi5_g4, map_mul, map_mul] at h1
    have h2 : (ψ.comp SemidirectProduct.inl) k8g4 *
        (ψ.comp SemidirectProduct.inl) k8g2 = (ψ.comp SemidirectProduct.inl) k8g4 := h1
    have h3 : (ψ.comp SemidirectProduct.inl) k8g4 * (ψ.comp SemidirectProduct.inl) k8g2 =
        (ψ.comp SemidirectProduct.inl) k8g4 * 1 := by rw [mul_one]; exact h2
    exact mul_left_cancel h3
  rcases order40_c4c2_unit_character_cases (ψ.comp SemidirectProduct.inl) with
    h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exfalso; rw [h, order40_chiC4C2_snd_two_g2] at hkey; exact absurd hkey (by decide)
  · exfalso; rw [h, order40_chiC4C2_prod_two_g2] at hkey; exact absurd hkey (by decide)
  · exact Or.inr (Or.inr (Or.inl h))
  · exfalso; rw [h, order40_chiC4C2_fst_four_snd_g2] at hkey; exact absurd hkey (by decide)
  · exact Or.inr (Or.inr (Or.inr h))
  · exfalso; rw [h, order40_chiC4C2_fst_four_inv_snd_g2] at hkey; exact absurd hkey (by decide)

/-- **Exhaustiveness for `K = Q₈ ⋊ C₂`** (`G₁₀`, action `ψ₆`).**  The character on the
`C₄`-generator must square to `1` (the same constraint as `G₈`). -/
theorem order80_classify_G10 (φ' : order16_wild_G10 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : order16_wild_G10 →* (ZMod 5)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨
        χ.comp SemidirectProduct.inl = order40_chiC4C2_fst_two ∨
        χ.comp SemidirectProduct.inl = order40_chiC4C2_snd_two ∨
        χ.comp SemidirectProduct.inl = order40_chiC4C2_prod_two) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  refine ⟨ψ, ?_, ⟨semidirectProductCongr_eq hψ⟩⟩
  have hkey : (ψ.comp SemidirectProduct.inl) k8g4 ^ 2 = 1 := by
    have h1 := hom_semidirectProduct_inl_invariant ψ
      (Multiplicative.ofAdd (1 : ZMod 2)) k8g4
    rw [show c2Action_psi6 (Multiplicative.ofAdd (1 : ZMod 2)) k8g4 = psi6 k8g4 from
      by rw [c2Action_psi6_gen], psi6_g4, map_inv, map_inv] at h1
    change ψ (SemidirectProduct.inl k8g4) ^ 2 = 1
    rw [sq]
    calc ψ (SemidirectProduct.inl k8g4) * ψ (SemidirectProduct.inl k8g4)
        = (ψ (SemidirectProduct.inl k8g4))⁻¹ * ψ (SemidirectProduct.inl k8g4) := by rw [h1]
      _ = 1 := inv_mul_cancel _
  rcases order40_c4c2_unit_character_cases (ψ.comp SemidirectProduct.inl) with
    h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exfalso; rw [h, order40_chiC4C2_fst_four_g4] at hkey; exact absurd hkey (by decide)
  · exfalso; rw [h, order40_chiC4C2_fst_four_snd_g4] at hkey; exact absurd hkey (by decide)
  · exfalso; rw [h, order40_chiC4C2_fst_four_inv_g4] at hkey; exact absurd hkey (by decide)
  · exfalso; rw [h, order40_chiC4C2_fst_four_inv_snd_g4] at hkey; exact absurd hkey (by decide)

/-! ### `K = C₁₆` (`G₆`, cyclic).  Stated for the concrete model `Multiplicative (ZMod 16)`;
`order16_wild_G6 ≃* Multiplicative (ZMod 16)` via `order16_A1_iso_concrete`. -/

theorem c16_hom_ext {M : Type*} [Monoid M] {χ ψ : Multiplicative (ZMod 16) →* M}
    (h : χ (Multiplicative.ofAdd (1 : ZMod 16)) = ψ (Multiplicative.ofAdd (1 : ZMod 16))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  let n : ZMod 16 := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 16)) ^ n.val := by
    rw [show x = Multiplicative.ofAdd n from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 16)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (n.val • (1 : ZMod 16)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 16)) ^ n.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, h]

/-- **Exhaustiveness for `K = C₁₆` (`G₆`).**  No constraint arises: all four characters of
`(ZMod 5)ˣ`-order dividing `4` occur (unconstrained, since `16`'s exponent is a multiple of
`(ZMod 5)ˣ`'s exponent `4`). -/
theorem order80_classify_C16 (φ' : Multiplicative (ZMod 16) →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : Multiplicative (ZMod 16) →* (ZMod 5)ˣ,
      (χ = 1 ∨ χ = powHom (p := 5) (q := 16) order40_u4 (by decide) ∨
        χ = powHom (p := 5) (q := 16) (order40_u4 ^ 2) (by decide) ∨
        χ = powHom (p := 5) (q := 16) (order40_u4 ^ 3) (by decide)) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16))
          (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  refine ⟨ψ, ?_, ⟨semidirectProductCongr_eq hψ⟩⟩
  rcases order40_unit_cases (ψ (Multiplicative.ofAdd (1 : ZMod 16))) with h | h | h | h
  · exact Or.inl (c16_hom_ext (by simp [h]))
  · exact Or.inr (Or.inl (c16_hom_ext (by rw [h]; decide)))
  · exact Or.inr (Or.inr (Or.inl (c16_hom_ext (by rw [h]; decide))))
  · exact Or.inr (Or.inr (Or.inr (c16_hom_ext (by rw [h]; decide))))

/-! ### `K = C₄` (auxiliary): character case-split reused for `G₁₂`, `G₁₃` -/

/-- Homomorphisms out of `Multiplicative (ZMod 4)` are determined by the generator. -/
theorem c4_hom_ext {M : Type*} [Monoid M] {χ ψ : Multiplicative (ZMod 4) →* M}
    (h : χ (Multiplicative.ofAdd (1 : ZMod 4)) = ψ (Multiplicative.ofAdd (1 : ZMod 4))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  let n : ZMod 4 := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 4)) ^ n.val := by
    rw [show x = Multiplicative.ofAdd n from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 4)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (n.val • (1 : ZMod 4)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 4)) ^ n.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, h]

/-- Characters `Multiplicative (ZMod 4) → (ZMod 5)ˣ` are one of the four order-dividing-`4`
characters. -/
theorem c4_unit_character_cases (χ : Multiplicative (ZMod 4) →* (ZMod 5)ˣ) :
    χ = 1 ∨ χ = powHom (p := 5) (q := 4) order40_u4 (by decide) ∨
      χ = powHom (p := 5) (q := 4) (order40_u4 ^ 2) (by decide) ∨
      χ = powHom (p := 5) (q := 4) (order40_u4 ^ 3) (by decide) := by
  rcases order40_unit_cases (χ (Multiplicative.ofAdd (1 : ZMod 4))) with h | h | h | h
  · exact Or.inl (c4_hom_ext (by simp [h]))
  · exact Or.inr (Or.inl (c4_hom_ext (by rw [h]; decide)))
  · exact Or.inr (Or.inr (Or.inl (c4_hom_ext (by rw [h]; decide))))
  · exact Or.inr (Or.inr (Or.inr (c4_hom_ext (by rw [h]; decide))))

/-! ### The direct-product family: `G₁ = C₈ × C₂`, `G₇ = K₈ × C₂`, `G₁₁ = Q₈ × C₂`

These `K`'s are literal direct products, so a character `χ : K →* (ZMod 5)ˣ` is simply an
independent pair of characters on the two factors (`MonoidHom.coprod_unique`), with no
invariance constraint (unlike the semidirect-product families above). -/

/-- **Exhaustiveness for `K = C₈ × C₂` (`G₁`).**  No constraint links the two factors. -/
theorem order80_classify_G1 (φ' : order16_wild_G1 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : order16_wild_G1 →* (ZMod 5)ˣ,
      (χ.comp (MonoidHom.inl _ _) = 1 ∨ χ.comp (MonoidHom.inl _ _) = order40_chiC8_four ∨
        χ.comp (MonoidHom.inl _ _) = order40_chiC8_two ∨
        χ.comp (MonoidHom.inl _ _) = order40_chiC8_four_inv) ∧
      (χ.comp (MonoidHom.inr _ _) = 1 ∨ χ.comp (MonoidHom.inr _ _) = order40_c2UnitHom) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, order40_c8_unit_character_cases _, c2_unit_character_cases _,
    ⟨semidirectProductCongr_eq hψ⟩⟩

/-- **Exhaustiveness for `K = K₈ × C₂ = C₄ × C₂ × C₂` (`G₇`).**  No constraint links the
factors. -/
theorem order80_classify_G7 (φ' : order16_wild_G7 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : order16_wild_G7 →* (ZMod 5)ˣ,
      (χ.comp (MonoidHom.inl _ _) = 1 ∨ χ.comp (MonoidHom.inl _ _) = order40_chiC4C2_fst_two ∨
        χ.comp (MonoidHom.inl _ _) = order40_chiC4C2_snd_two ∨
        χ.comp (MonoidHom.inl _ _) = order40_chiC4C2_prod_two ∨
        χ.comp (MonoidHom.inl _ _) = order40_chiC4C2_fst_four ∨
        χ.comp (MonoidHom.inl _ _) = order40_chiC4C2_fst_four_snd ∨
        χ.comp (MonoidHom.inl _ _) = order40_chiC4C2_fst_four_inv ∨
        χ.comp (MonoidHom.inl _ _) = order40_chiC4C2_fst_four_inv_snd) ∧
      (χ.comp (MonoidHom.inr _ _) = 1 ∨ χ.comp (MonoidHom.inr _ _) = order40_c2UnitHom) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, order40_c4c2_unit_character_cases _, c2_unit_character_cases _,
    ⟨semidirectProductCongr_eq hψ⟩⟩

/-- **Exhaustiveness for `K = Q₈ × C₂` (`G₁₁`).**  No constraint links the factors. -/
theorem order80_classify_G11 (φ' : order16_wild_G11 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : order16_wild_G11 →* (ZMod 5)ˣ,
      (χ.comp (MonoidHom.inl _ _) = 1 ∨ χ.comp (MonoidHom.inl _ _) = order40_chiQ8 ∨
        χ.comp (MonoidHom.inl _ _) = order40_chiQ8_xa ∨
        χ.comp (MonoidHom.inl _ _) = order40_chiQ8_prod) ∧
      (χ.comp (MonoidHom.inr _ _) = 1 ∨ χ.comp (MonoidHom.inr _ _) = order40_c2UnitHom) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11 (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, order40_q8_unit_character_cases _, c2_unit_character_cases _,
    ⟨semidirectProductCongr_eq hψ⟩⟩

/-! ### `K = C₄ ⋊ C₄` (`G₁₂ = order16_N3`, inversion action `x ↦ x³`) -/

/-- The generator computation for `c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4`: it sends the
generator of the acting `C₄` to the automorphism cubing the acted-on `C₄`. -/
theorem c4ActionAut3_gen :
    c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 (Multiplicative.ofAdd (1 : ZMod 4))
      (Multiplicative.ofAdd (1 : ZMod 4)) = (Multiplicative.ofAdd (1 : ZMod 4)) ^ 3 := by
  have hc4 : c4UnitHom 4 zmod4_unit_3 zmod4_unit_3_pow4 (Multiplicative.ofAdd (1 : ZMod 4)) =
      zmod4_unit_3 := by decide
  change (unitAut 4).comp (c4UnitHom 4 zmod4_unit_3 zmod4_unit_3_pow4)
    (Multiplicative.ofAdd (1 : ZMod 4)) (Multiplicative.ofAdd (1 : ZMod 4)) = _
  rw [MonoidHom.comp_apply, hc4, unitAut_ofAdd_one,
    show (zmod4_unit_3 : ZMod 4).val = 3 from by decide]

/-- **Exhaustiveness for `K = C₄ ⋊ C₄` (`G₁₂`, inversion action).**  The character on the
normal `C₄`-factor must square to `1`. -/
theorem order80_classify_G12 (φ' : order16_wild_G12 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : order16_wild_G12 →* (ZMod 5)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨
        χ.comp SemidirectProduct.inl = powHom (p := 5) (q := 4) order40_u4 (by decide) ∨
        χ.comp SemidirectProduct.inl = powHom (p := 5) (q := 4) (order40_u4 ^ 2) (by decide) ∨
        χ.comp SemidirectProduct.inl = powHom (p := 5) (q := 4) (order40_u4 ^ 3) (by decide)) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  refine ⟨ψ, ?_, ⟨semidirectProductCongr_eq hψ⟩⟩
  set χA := ψ.comp SemidirectProduct.inl with hχA
  set g : Multiplicative (ZMod 4) := Multiplicative.ofAdd (1 : ZMod 4) with hg
  have hkey : χA g ^ 3 = χA g := by
    have h1 := hom_semidirectProduct_inl_invariant ψ g g
    rw [show (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4) g g = g ^ 3 from
      c4ActionAut3_gen, map_pow, map_pow] at h1
    exact h1
  have hsq : χA g ^ 2 = 1 := by
    have := congrArg (· * (χA g)⁻¹) hkey
    simpa [pow_succ, mul_assoc] using this
  rcases c4_unit_character_cases χA with h | h | h | h
  · exact Or.inl h
  · exfalso
    rw [h] at hsq
    exact absurd hsq (by decide)
  · exact Or.inr (Or.inr (Or.inl h))
  · exfalso
    rw [h] at hsq
    exact absurd hsq (by decide)

/-! ### `K = C₄ × C₄` (`G₁₃`), stated on the concrete model.  `order16_wild_G13 = order16_A3
≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)` via `order16_A3_iso_concrete`. -/

/-- **Exhaustiveness for `K = C₄ × C₄` (`G₁₃`).**  No constraint links the two factors. -/
theorem order80_classify_G13
    (φ' : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →*
      MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →* (ZMod 5)ˣ,
      (χ.comp (MonoidHom.inl _ _) = 1 ∨
        χ.comp (MonoidHom.inl _ _) = powHom (p := 5) (q := 4) order40_u4 (by decide) ∨
        χ.comp (MonoidHom.inl _ _) = powHom (p := 5) (q := 4) (order40_u4 ^ 2) (by decide) ∨
        χ.comp (MonoidHom.inl _ _) = powHom (p := 5) (q := 4) (order40_u4 ^ 3) (by decide)) ∧
      (χ.comp (MonoidHom.inr _ _) = 1 ∨
        χ.comp (MonoidHom.inr _ _) = powHom (p := 5) (q := 4) order40_u4 (by decide) ∨
        χ.comp (MonoidHom.inr _ _) = powHom (p := 5) (q := 4) (order40_u4 ^ 2) (by decide) ∨
        χ.comp (MonoidHom.inr _ _) = powHom (p := 5) (q := 4) (order40_u4 ^ 3) (by decide)) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, c4_unit_character_cases _, c4_unit_character_cases _,
    ⟨semidirectProductCongr_eq hψ⟩⟩

/-! ### `K = (C₂)⁴` (`G₀`), stated on the concrete model.  `order16_wild_G0 = order16_A5
≃* order16_wild_C2pow4` via `order16_A5_iso_concrete`. -/

/-- **Exhaustiveness for `K = (C₂)⁴` (`G₀`).**  No constraint links the four factors. -/
theorem order80_classify_G0 (φ' : order16_wild_C2pow4 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : order16_wild_C2pow4 →* (ZMod 5)ˣ,
      (χ.comp (MonoidHom.inl _ _) = 1 ∨ χ.comp (MonoidHom.inl _ _) = order40_c2UnitHom) ∧
      ((χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inl _ _) = 1 ∨
        (χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inl _ _) = order40_c2UnitHom) ∧
      (((χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)).comp (MonoidHom.inl _ _) = 1 ∨
        ((χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)).comp (MonoidHom.inl _ _) =
          order40_c2UnitHom) ∧
      (((χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _) = 1 ∨
        ((χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _) =
          order40_c2UnitHom) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4 (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, c2_unit_character_cases _, c2_unit_character_cases _, c2_unit_character_cases _,
    c2_unit_character_cases _, ⟨semidirectProductCongr_eq hψ⟩⟩

/-! ### `K = Q₁₆` (`G₅ = QuaternionGroup 4`, generalised quaternion) -/

/-- A representative `Q₁₆ → C₂` character, nontrivial on the order-`8` generator `a 1`. -/
noncomputable def order80_chiQ16 : QuaternionGroup 4 →* Multiplicative (ZMod 2) where
  toFun
    | QuaternionGroup.a i => Multiplicative.ofAdd ((ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)) i)
    | QuaternionGroup.xa i =>
      Multiplicative.ofAdd ((ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)) i)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · simp [QuaternionGroup.a_mul_a, map_add, ofAdd_add]
    · simp only [QuaternionGroup.a_mul_xa]
      apply_fun Multiplicative.toAdd
      simp [toAdd_mul, sub_eq_add_neg, CharTwo.neg_eq]
      ac_rfl
    · simp [QuaternionGroup.xa_mul_a, map_add, ofAdd_add]
    · simp only [QuaternionGroup.xa_mul_xa]
      apply_fun Multiplicative.toAdd
      simp [toAdd_mul, sub_eq_add_neg, CharTwo.neg_eq]
      ac_rfl

/-- The `Q₁₆ → C₂` character nontrivial on `xa 0`. -/
noncomputable def order80_chiQ16_xa : QuaternionGroup 4 →* Multiplicative (ZMod 2) where
  toFun
    | QuaternionGroup.a _ => 1
    | QuaternionGroup.xa _ => Multiplicative.ofAdd (1 : ZMod 2)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · rfl
    · rfl
    · rfl
    · simp only [QuaternionGroup.xa_mul_xa]
      decide

/-- The product of the two displayed `Q₁₆ → C₂` characters. -/
noncomputable abbrev order80_chiQ16_prod : QuaternionGroup 4 →* Multiplicative (ZMod 2) :=
  order80_chiQ16 * order80_chiQ16_xa

noncomputable abbrev order80_chiQ16_c5 : QuaternionGroup 4 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order80_chiQ16

noncomputable abbrev order80_chiQ16_xa_c5 : QuaternionGroup 4 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order80_chiQ16_xa

noncomputable abbrev order80_chiQ16_prod_c5 : QuaternionGroup 4 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.comp order80_chiQ16_prod

@[simp] theorem order80_chiQ16_c5_a1 :
    order80_chiQ16_c5 (QuaternionGroup.a (1 : ZMod 8)) = order40_u4 ^ 2 := by decide

@[simp] theorem order80_chiQ16_c5_x0 :
    order80_chiQ16_c5 (QuaternionGroup.xa (0 : ZMod 8)) = 1 := by decide

@[simp] theorem order80_chiQ16_xa_c5_a1 :
    order80_chiQ16_xa_c5 (QuaternionGroup.a (1 : ZMod 8)) = 1 := by decide

@[simp] theorem order80_chiQ16_xa_c5_x0 :
    order80_chiQ16_xa_c5 (QuaternionGroup.xa (0 : ZMod 8)) = order40_u4 ^ 2 := by decide

@[simp] theorem order80_chiQ16_prod_c5_a1 :
    order80_chiQ16_prod_c5 (QuaternionGroup.a (1 : ZMod 8)) = order40_u4 ^ 2 := by decide

@[simp] theorem order80_chiQ16_prod_c5_x0 :
    order80_chiQ16_prod_c5 (QuaternionGroup.xa (0 : ZMod 8)) = order40_u4 ^ 2 := by decide

/-- Homomorphisms out of `Q₁₆` are determined by the two displayed generators. -/
theorem order80_q16_hom_ext {M : Type} [Group M] {χ ψ : QuaternionGroup 4 →* M}
    (ha : χ (QuaternionGroup.a (1 : ZMod 8)) = ψ (QuaternionGroup.a (1 : ZMod 8)))
    (hx : χ (QuaternionGroup.xa (0 : ZMod 8)) = ψ (QuaternionGroup.xa (0 : ZMod 8))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases x with i | i
  · have hi : QuaternionGroup.a i =
        (QuaternionGroup.a (1 : ZMod 8) : QuaternionGroup 4) ^ i.val := by
      calc
        QuaternionGroup.a i = QuaternionGroup.a ((i.val : ZMod 8)) := by
          rw [ZMod.natCast_zmod_val]
        _ = (QuaternionGroup.a (1 : ZMod 8) : QuaternionGroup 4) ^ i.val := by
          rw [QuaternionGroup.a_one_pow]
    rw [hi, map_pow, map_pow, ha]
  · have hai : QuaternionGroup.a i =
        (QuaternionGroup.a (1 : ZMod 8) : QuaternionGroup 4) ^ i.val := by
      calc
        QuaternionGroup.a i = QuaternionGroup.a ((i.val : ZMod 8)) := by
          rw [ZMod.natCast_zmod_val]
        _ = (QuaternionGroup.a (1 : ZMod 8) : QuaternionGroup 4) ^ i.val := by
          rw [QuaternionGroup.a_one_pow]
    have hi : QuaternionGroup.xa i =
        QuaternionGroup.xa (0 : ZMod 8) *
          (QuaternionGroup.a (1 : ZMod 8) : QuaternionGroup 4) ^ i.val := by
      rw [← hai]
      simp [QuaternionGroup.xa_mul_a]
    rw [hi, map_mul, map_mul, map_pow, map_pow, hx, ha]

/-- The conjugation relation forces the character on `a 1` to square to `1`. -/
theorem order80_q16_character_a_sq (χ : QuaternionGroup 4 →* (ZMod 5)ˣ) :
    χ (QuaternionGroup.a (1 : ZMod 8)) ^ 2 = 1 := by
  let a1 : QuaternionGroup 4 := QuaternionGroup.a (1 : ZMod 8)
  let x0 : QuaternionGroup 4 := QuaternionGroup.xa (0 : ZMod 8)
  have hrel : x0 * a1 = a1⁻¹ * x0 := by decide
  have himg : χ (x0 * a1) = χ (a1⁻¹ * x0) := congrArg χ hrel
  rw [map_mul, map_mul, map_inv] at himg
  have hmul : χ a1 = (χ a1)⁻¹ := by
    have := congrArg (fun x => x * (χ x0)⁻¹) himg
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  rw [pow_two]
  nth_rw 2 [hmul]
  exact mul_inv_cancel _

/-- The relation `(xa 0)² = (a 1)⁴` transports the previous constraint to `xa 0`. -/
theorem order80_q16_character_x_sq (χ : QuaternionGroup 4 →* (ZMod 5)ˣ)
    (ha : χ (QuaternionGroup.a (1 : ZMod 8)) ^ 2 = 1) :
    χ (QuaternionGroup.xa (0 : ZMod 8)) ^ 2 = 1 := by
  let a1 : QuaternionGroup 4 := QuaternionGroup.a (1 : ZMod 8)
  let x0 : QuaternionGroup 4 := QuaternionGroup.xa (0 : ZMod 8)
  have hrel : x0 ^ 2 = a1 ^ 4 := by decide
  have himg : χ (x0 ^ 2) = χ (a1 ^ 4) := congrArg χ hrel
  rw [map_pow, map_pow] at himg
  change χ x0 ^ 2 = 1
  rw [himg]
  change χ a1 ^ (2 * 2) = 1
  rw [pow_mul, ha, one_pow]

/-- **Exhaustiveness for `K = Q₁₆` (`G₅`).**  A character `Q₁₆ → (ZMod 5)ˣ` is one of the four
displayed characters. -/
theorem order80_q16_unit_character_cases (χ : QuaternionGroup 4 →* (ZMod 5)ˣ) :
    χ = 1 ∨ χ = order80_chiQ16_c5 ∨ χ = order80_chiQ16_xa_c5 ∨ χ = order80_chiQ16_prod_c5 := by
  let a1 : QuaternionGroup 4 := QuaternionGroup.a (1 : ZMod 8)
  let x0 : QuaternionGroup 4 := QuaternionGroup.xa (0 : ZMod 8)
  have hsq_a : χ a1 ^ 2 = 1 := order80_q16_character_a_sq χ
  have hsq_x : χ x0 ^ 2 = 1 := order80_q16_character_x_sq χ hsq_a
  rcases order40_unit_sq_eq_one_cases (χ a1) hsq_a with ha | ha <;>
    rcases order40_unit_sq_eq_one_cases (χ x0) hsq_x with hx | hx
  · left
    apply order80_q16_hom_ext <;> simp [a1, x0, ha, hx]
  · right
    right
    left
    apply order80_q16_hom_ext <;> simp [a1, x0, ha, hx]
  · right
    left
    apply order80_q16_hom_ext <;> simp [a1, x0, ha, hx]
  · right
    right
    right
    apply order80_q16_hom_ext <;> simp [a1, x0, ha, hx]

/-- **Exhaustiveness for `K = Q₁₆` (`G₅`, action classification).** -/
theorem order80_classify_G5 (φ' : QuaternionGroup 4 →* MulAut (Multiplicative (ZMod 5))) :
    ∃ χ : QuaternionGroup 4 →* (ZMod 5)ˣ,
      (χ = 1 ∨ χ = order80_chiQ16_c5 ∨ χ = order80_chiQ16_xa_c5 ∨ χ = order80_chiQ16_prod_c5) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4) (unitAutHom.comp χ)) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, order80_q16_unit_character_cases ψ, ⟨semidirectProductCongr_eq hψ⟩⟩

end Smallgroups.UsefulTheorems
