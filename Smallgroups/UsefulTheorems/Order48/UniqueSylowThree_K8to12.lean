/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.UniqueSylowThree
import Smallgroups.UsefulTheorems.Order80.UniqueSylowFive_K1to7

/-!
# Isomorphism classes of `C₃ ⋊ Kᵢ` for `i = 8, 9, 10, 11, 12`

Continues `Order48/UniqueSylowThree.lean` (machinery and the `C₈`-extension family
`G₂, G₃, G₄`) for the five hardest kernels of the Sylow-`3`-unique branch of the
order-`48` classification:

* `K₈ = D₈ × C₂ = K₈g ⋊[ψ₃] C₂` (`order16_wild_G8`),
* `K₉ = K₈g ⋊[ψ₅] C₂` (`order16_wild_G9`),
* `K₁₀ = C₄ ∘ D₄ = K₈g ⋊[ψ₆] C₂` (`order16_wild_G10`, the Pauli group),
* `K₁₁ = Q₈ × C₂` (`order16_wild_G11`),
* `K₁₂ = C₄ ⋊ C₄` (`order16_wild_G12 = order16_N3`).

This mirrors `Order80/UniqueSylowFive_K0_K8to13.lean`, which treats the SAME five
kernels for `(ZMod 5)ˣ`-valued characters.  The `(ZMod 3)ˣ = {±1}` situation is
simpler: every character is determined by an index-`≤2` subgroup, so the order-`4`
characters of the order-`80` analysis disappear and several invariance constraints
become automatic (`χ(x)⁻¹ = χ(x)` holds for `±1`-valued `χ`).  Concretely:

* for `K₈` (ψ₃ inverts the `C₄`-generator) all four `±1`-characters of `K8g` are
  ψ₃-invariant, giving `8` raw candidates and `4` orbits;
* for `K₉` (ψ₅ sends `g₄ ↦ g₄g₂`) the invariance `χ(g₂) = 1` still bites, leaving
  `{1, fst}` on the `K8g`-part, `4` raw candidates and `3` orbits;
* for `K₁₀` (ψ₆ inverts the `C₄`-generator) all four `±1`-characters are invariant,
  `8` raw candidates and `4` orbits;
* for `K₁₁` (direct product, no constraint) `4 · 2 = 8` raw candidates, `3` orbits;
* for `K₁₂` (inversion action on the normal `C₄`) the constraint `χ(a)³ = χ(a)` is
  automatic, `2 · 2 = 4` raw candidates and `3` orbits.

Total: `4 + 3 + 4 + 3 + 3 = 17` classes.
-/

namespace Smallgroups.UsefulTheorems

/-! ## The `±1` character toolkit: `C₄`, `C₄ × C₂`, and `Q₈` characters -/

/-- The sign character `C₄ →* (ZMod 3)ˣ`, sending the generator to `-1`. -/
noncomputable abbrev order48_signC4 : Multiplicative (ZMod 4) →* (ZMod 3)ˣ :=
  powHom (p := 3) (q := 4) (-1) (by decide)

@[simp]
theorem order48_signC4_gen : order48_signC4 (Multiplicative.ofAdd (1 : ZMod 4)) = -1 := by
  decide

/-- Characters `C₄ → (ZMod 3)ˣ` are trivial or `order48_signC4`. -/
theorem c4_zmod3_character_cases (χ : Multiplicative (ZMod 4) →* (ZMod 3)ˣ) :
    χ = 1 ∨ χ = order48_signC4 := by
  rcases zmod3_unit_eq_one_or_neg (χ (Multiplicative.ofAdd (1 : ZMod 4))) with h | h
  · exact Or.inl (multiplicative_zmod_hom_ext (by simp [h]))
  · exact Or.inr (multiplicative_zmod_hom_ext (by rw [h, order48_signC4_gen]))

/-- Sign on the `C₄`-factor of `K8g = C₄ × C₂`. -/
noncomputable abbrev order48_chiC4C2_fst : K8g →* (ZMod 3)ˣ :=
  order48_signC4.comp (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)))

/-- Sign on the `C₂`-factor of `K8g = C₄ × C₂`. -/
noncomputable abbrev order48_chiC4C2_snd : K8g →* (ZMod 3)ˣ :=
  order48_signC2.comp (MonoidHom.snd (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)))

/-- Sign on both factors of `K8g = C₄ × C₂`. -/
noncomputable abbrev order48_chiC4C2_prod : K8g →* (ZMod 3)ˣ :=
  order48_chiC4C2_fst * order48_chiC4C2_snd

@[simp]
theorem order48_chiC4C2_fst_g4 : order48_chiC4C2_fst k8g4 = -1 := by decide
@[simp]
theorem order48_chiC4C2_fst_g2 : order48_chiC4C2_fst k8g2 = 1 := by decide
@[simp]
theorem order48_chiC4C2_snd_g4 : order48_chiC4C2_snd k8g4 = 1 := by decide
@[simp]
theorem order48_chiC4C2_snd_g2 : order48_chiC4C2_snd k8g2 = -1 := by decide
@[simp]
theorem order48_chiC4C2_prod_g4 : order48_chiC4C2_prod k8g4 = -1 := by decide
@[simp]
theorem order48_chiC4C2_prod_g2 : order48_chiC4C2_prod k8g2 = -1 := by decide

/-- Characters `K8g = C₄ × C₂ → (ZMod 3)ˣ` are one of the four displayed characters. -/
theorem order48_c4c2_zmod3_character_cases (χ : K8g →* (ZMod 3)ˣ) :
    χ = 1 ∨ χ = order48_chiC4C2_fst ∨ χ = order48_chiC4C2_snd ∨
      χ = order48_chiC4C2_prod := by
  rcases zmod3_unit_eq_one_or_neg (χ k8g4) with h4 | h4 <;>
    rcases zmod3_unit_eq_one_or_neg (χ k8g2) with h2 | h2
  · exact Or.inl (order40_c4c2_hom_ext (by rw [h4]; decide) (by rw [h2]; decide))
  · exact Or.inr (Or.inr (Or.inl
      (order40_c4c2_hom_ext (by rw [h4]; decide) (by rw [h2]; decide))))
  · exact Or.inr (Or.inl (order40_c4c2_hom_ext (by rw [h4]; decide) (by rw [h2]; decide)))
  · exact Or.inr (Or.inr (Or.inr
      (order40_c4c2_hom_ext (by rw [h4]; decide) (by rw [h2]; decide))))

/-- The `(ZMod 3)ˣ`-valued `Q₈` characters, via the `Q₈ → C₂` characters of `Order88.lean`. -/
noncomputable abbrev order48_chiQ8 : QuaternionGroup 2 →* (ZMod 3)ˣ :=
  order48_signC2.comp order88_chiQ8
noncomputable abbrev order48_chiQ8_xa : QuaternionGroup 2 →* (ZMod 3)ˣ :=
  order48_signC2.comp order88_chiQ8_xa
noncomputable abbrev order48_chiQ8_prod : QuaternionGroup 2 →* (ZMod 3)ˣ :=
  order48_signC2.comp order88_chiQ8_prod

/-- Characters `Q₈ → (ZMod 3)ˣ` are determined by `a 1` and `xa 0`. -/
theorem order48_q8_hom_ext {χ ψ : QuaternionGroup 2 →* (ZMod 3)ˣ}
    (ha : χ (QuaternionGroup.a (1 : ZMod 4)) = ψ (QuaternionGroup.a (1 : ZMod 4)))
    (hx : χ (QuaternionGroup.xa (0 : ZMod 4)) = ψ (QuaternionGroup.xa (0 : ZMod 4))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases x with i | i
  · have hi : QuaternionGroup.a i =
        (QuaternionGroup.a (1 : ZMod 4) : QuaternionGroup 2) ^ i.val := by
      calc
        QuaternionGroup.a i = QuaternionGroup.a ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = (QuaternionGroup.a (1 : ZMod 4) : QuaternionGroup 2) ^ i.val := by
          rw [QuaternionGroup.a_one_pow]
    rw [hi, map_pow, map_pow, ha]
  · have hai : QuaternionGroup.a i =
        (QuaternionGroup.a (1 : ZMod 4) : QuaternionGroup 2) ^ i.val := by
      calc
        QuaternionGroup.a i = QuaternionGroup.a ((i.val : ZMod 4)) := by
          rw [ZMod.natCast_zmod_val]
        _ = (QuaternionGroup.a (1 : ZMod 4) : QuaternionGroup 2) ^ i.val := by
          rw [QuaternionGroup.a_one_pow]
    have hi : QuaternionGroup.xa i =
        QuaternionGroup.xa (0 : ZMod 4) *
          (QuaternionGroup.a (1 : ZMod 4) : QuaternionGroup 2) ^ i.val := by
      rw [← hai]
      simp [QuaternionGroup.xa_mul_a]
    rw [hi, map_mul, map_mul, map_pow, map_pow, hx, ha]

/-- A character `Q₈ → (ZMod 3)ˣ` is one of the four displayed characters. -/
theorem order48_q8_zmod3_character_cases (χ : QuaternionGroup 2 →* (ZMod 3)ˣ) :
    χ = 1 ∨ χ = order48_chiQ8 ∨ χ = order48_chiQ8_xa ∨
      χ = order48_chiQ8_prod := by
  rcases zmod3_unit_eq_one_or_neg (χ (QuaternionGroup.a (1 : ZMod 4))) with ha | ha <;>
    rcases zmod3_unit_eq_one_or_neg (χ (QuaternionGroup.xa (0 : ZMod 4))) with hx | hx
  · exact Or.inl (order48_q8_hom_ext (by rw [ha]; decide) (by rw [hx]; decide))
  · exact Or.inr (Or.inr (Or.inl
      (order48_q8_hom_ext (by rw [ha]; decide) (by rw [hx]; decide))))
  · exact Or.inr (Or.inl (order48_q8_hom_ext (by rw [ha]; decide) (by rw [hx]; decide)))
  · exact Or.inr (Or.inr (Or.inr
      (order48_q8_hom_ext (by rw [ha]; decide) (by rw [hx]; decide))))

/-! ## `K₈ = D₈ × C₂ = K₈g ⋊[ψ₃] C₂`

The ψ₃-invariance constraint `χ(ψ₃ g₄) = χ(g₄)`, i.e. `χ(g₄)⁻¹ = χ(g₄)`, is
automatic for `±1`-valued characters, so all four `K8g`-characters occur. -/

/-- **Exhaustiveness for `K = D₈ × C₂` (`G₈`, action `ψ₃ : (x,y) ↦ (x⁻¹,y)`).**  No
constraint arises for `±1`-valued characters: ψ₃ inverts the `C₄`-generator and
`u⁻¹ = u` for `u ∈ {±1}`. -/
theorem order48_classify_G8 (φ' : order16_wild_G8 →* MulAut (Multiplicative (ZMod 3))) :
    ∃ χ : order16_wild_G8 →* (ZMod 3)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨
        χ.comp SemidirectProduct.inl = order48_chiC4C2_fst ∨
        χ.comp SemidirectProduct.inl = order48_chiC4C2_snd ∨
        χ.comp SemidirectProduct.inl = order48_chiC4C2_prod) ∧
      (χ.comp SemidirectProduct.inr = 1 ∨ χ.comp SemidirectProduct.inr = order48_signC2) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8 (order48_action χ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, order48_c4c2_zmod3_character_cases _, c2_zmod3_character_cases _,
    ⟨semidirectProductCongr_eq hψ⟩⟩

theorem order48_K8_chiC4C2_one_invariant :
    ∀ b, (1 : K8g →* (ZMod 3)ˣ).comp (c2Action_psi3 b).toMonoidHom = 1 :=
  fun _ => by ext; simp

theorem order48_K8_chiC4C2_fst_invariant :
    ∀ b, order48_chiC4C2_fst.comp (c2Action_psi3 b).toMonoidHom = order48_chiC4C2_fst := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi3 _ from
        by rw [c2Action_psi3_gen]] <;>
    decide

theorem order48_K8_chiC4C2_snd_invariant :
    ∀ b, order48_chiC4C2_snd.comp (c2Action_psi3 b).toMonoidHom = order48_chiC4C2_snd := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi3 _ from
        by rw [c2Action_psi3_gen]] <;>
    decide

theorem order48_K8_chiC4C2_prod_invariant :
    ∀ b, order48_chiC4C2_prod.comp (c2Action_psi3 b).toMonoidHom = order48_chiC4C2_prod := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi3 _ from
        by rw [c2Action_psi3_gen]] <;>
    decide

noncomputable abbrev order48_K8_chi_00 : order16_wild_G8 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 1
    (fun b => by rw [order48_K8_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K8_chi_02 : order16_wild_G8 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 order48_signC2
    (fun b => by rw [order48_K8_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K8_chi_f0 : order16_wild_G8 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_fst 1
    (fun b => by rw [order48_K8_chiC4C2_fst_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K8_chi_f2 : order16_wild_G8 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_fst order48_signC2
    (fun b => by rw [order48_K8_chiC4C2_fst_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K8_chi_s0 : order16_wild_G8 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_snd 1
    (fun b => by rw [order48_K8_chiC4C2_snd_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K8_chi_s2 : order16_wild_G8 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_snd order48_signC2
    (fun b => by rw [order48_K8_chiC4C2_snd_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K8_chi_p0 : order16_wild_G8 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_prod 1
    (fun b => by rw [order48_K8_chiC4C2_prod_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K8_chi_p2 : order16_wild_G8 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_prod order48_signC2
    (fun b => by rw [order48_K8_chiC4C2_prod_invariant, mulAut_conj_of_comm]; ext a; simp)

/-- **The `K₈g`-shear `(a,b) ↦ (a, b·π(a))`, `π : C₄ → C₂` the mod-`2` projection**: commutes
with `ψ₃` (both sides invert `a`, fix the shift), hence extends to an automorphism of `K₈`.
Merges `snd` with `prod` (adding `fst`'s value into the shift). -/
noncomputable def order48_K8g_shear2 : K8g ≃* K8g where
  toFun p := (p.1, p.2 * k8Proj p.1)
  invFun p := (p.1, p.2 * k8Proj p.1)
  left_inv p := by ext; · rfl
                   · change p.2 * k8Proj p.1 * k8Proj p.1 = p.2
                     rw [mul_assoc, k8Proj_self_mul, mul_one]
  right_inv p := by ext; · rfl
                    · change p.2 * k8Proj p.1 * k8Proj p.1 = p.2
                      rw [mul_assoc, k8Proj_self_mul, mul_one]
  map_mul' p q := by
    rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
    ext <;> revert p1 p2 q1 q2 <;> decide

/-- `order48_K8g_shear2` embedded into `order16_wild_G8` via `inl`. -/
noncomputable def order48_K8_shear2_inl : K8g →* order16_wild_G8 :=
  (SemidirectProduct.inl : K8g →* order16_wild_G8).comp order48_K8g_shear2.toMonoidHom

theorem order48_K8g_shear2_comp_psi3 :
    ∀ b, order48_K8_shear2_inl.comp (c2Action_psi3 b).toMonoidHom =
      (MulAut.conj ((SemidirectProduct.inr : Multiplicative (ZMod 2) →* order16_wild_G8) b)
        ).toMonoidHom.comp order48_K8_shear2_inl := by
  intro b
  apply MonoidHom.ext
  intro a
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · simp [order48_K8_shear2_inl]
  · change SemidirectProduct.inl (order48_K8g_shear2 ((c2Action_psi3
    (Multiplicative.ofAdd (1 : ZMod 2))) a))
      = MulAut.conj (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)))
        (SemidirectProduct.inl (order48_K8g_shear2 a))
    rw [show c2Action_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) a = psi3 a from
        by rw [c2Action_psi3_gen], MulAut.conj_apply, ← map_inv, ← SemidirectProduct.inl_aut]
    congr 1
    revert a; decide

noncomputable def order48_K8_shear2 : order16_wild_G8 →* order16_wild_G8 :=
  SemidirectProduct.lift order48_K8_shear2_inl
    (SemidirectProduct.inr : Multiplicative (ZMod 2) →* order16_wild_G8)
    order48_K8g_shear2_comp_psi3

theorem order48_K8_shear2_bijective : Function.Bijective order48_K8_shear2 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def order48_K8_shear2_equiv : order16_wild_G8 ≃* order16_wild_G8 :=
  MulEquiv.ofBijective order48_K8_shear2 order48_K8_shear2_bijective

theorem order48_K8_chi_s0_comp_shear2 :
    order48_K8_chi_s0.comp order48_K8_shear2_equiv.toMonoidHom = order48_K8_chi_p0 := by
  apply MonoidHom.ext; decide
theorem order48_K8_chi_s2_comp_shear2 :
    order48_K8_chi_s2.comp order48_K8_shear2_equiv.toMonoidHom = order48_K8_chi_p2 := by
  apply MonoidHom.ext; decide

theorem order48_K8_iso_s0_p0 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G8 (order48_action order48_K8_chi_s0) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
      (order48_action order48_K8_chi_p0)) :=
  order48_semidirectProduct_of_comp_eq order48_K8_shear2_equiv order48_K8_chi_s0_comp_shear2
theorem order48_K8_iso_s2_p2 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G8 (order48_action order48_K8_chi_s2) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
      (order48_action order48_K8_chi_p2)) :=
  order48_semidirectProduct_of_comp_eq order48_K8_shear2_equiv order48_K8_chi_s2_comp_shear2

/-- **The OUTER shear `s ↦ s·k` for `k = inl(1,1)·inr(1)`**: toggles the outer `C₂`-character
whenever the `K8g`-part is nontrivial at `inl(1,1)` (i.e. for `fst` and `prod`), merging
`f0 = f2` and `p0 = p2`; it fixes `chi_00`, `chi_02` and the `snd`-family. -/
noncomputable def order48_K8_shearOuter_B : order16_wild_G8 :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 2))) *
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem order48_K8_shearOuter_B_pow2 : order48_K8_shearOuter_B ^ 2 = 1 := by decide

theorem order48_K8_shearOuter_compat :
    ∀ b, (SemidirectProduct.inl : K8g →* order16_wild_G8).comp (c2Action_psi3 b).toMonoidHom =
      (MulAut.conj ((C2_powHom order48_K8_shearOuter_B order48_K8_shearOuter_B_pow2) b)
        ).toMonoidHom.comp (SemidirectProduct.inl : K8g →* order16_wild_G8) := by
  intro b
  apply MonoidHom.ext
  intro a
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · simp
  · change SemidirectProduct.inl (psi3 a) =
      MulAut.conj (order48_K8_shearOuter_B) (SemidirectProduct.inl a)
    rw [MulAut.conj_apply, order48_K8_shearOuter_B]
    revert a; decide

noncomputable def order48_K8_shearOuter : order16_wild_G8 →* order16_wild_G8 :=
  SemidirectProduct.lift (SemidirectProduct.inl : K8g →* order16_wild_G8)
    (C2_powHom order48_K8_shearOuter_B order48_K8_shearOuter_B_pow2) order48_K8_shearOuter_compat

theorem order48_K8_shearOuter_bijective : Function.Bijective order48_K8_shearOuter := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def order48_K8_shearOuter_equiv : order16_wild_G8 ≃* order16_wild_G8 :=
  MulEquiv.ofBijective order48_K8_shearOuter order48_K8_shearOuter_bijective

theorem order48_K8_chi_f0_comp_shearOuter :
    order48_K8_chi_f0.comp order48_K8_shearOuter_equiv.toMonoidHom = order48_K8_chi_f2 := by
  apply MonoidHom.ext; decide
theorem order48_K8_chi_p0_comp_shearOuter :
    order48_K8_chi_p0.comp order48_K8_shearOuter_equiv.toMonoidHom = order48_K8_chi_p2 := by
  apply MonoidHom.ext; decide

theorem order48_K8_iso_f0_f2 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G8 (order48_action order48_K8_chi_f0) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
      (order48_action order48_K8_chi_f2)) :=
  order48_semidirectProduct_of_comp_eq order48_K8_shearOuter_equiv
    order48_K8_chi_f0_comp_shearOuter
theorem order48_K8_iso_p0_p2 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G8 (order48_action order48_K8_chi_p0) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
      (order48_action order48_K8_chi_p2)) :=
  order48_semidirectProduct_of_comp_eq order48_K8_shearOuter_equiv
    order48_K8_chi_p0_comp_shearOuter

/-- **`K₈ = D₈ × C₂` contributes exactly `4` isomorphism classes**: the `8` raw candidates
collapse via `order48_K8g_shear2` (`s0 = p0`, `s2 = p2`) and `order48_K8_shearOuter`
(`f0 = f2`, `p0 = p2`), chaining to `s0 = p0 = p2 = s2` — a single class — while `chi_00`,
`chi_f0` and `chi_02` remain separate orbits.  Representatives: `order48_K8_chi_00`,
`order48_K8_chi_f0` (`= chi_f2`), `order48_K8_chi_02`,
`order48_K8_chi_s0` (`= chi_p0 = chi_p2 = chi_s2`). -/
theorem order48_classify_K8_reduced (φ' : order16_wild_G8 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
          (order48_action order48_K8_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
          (order48_action order48_K8_chi_f0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
          (order48_action order48_K8_chi_02)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G8
          (order48_action order48_K8_chi_s0)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order48_classify_G8 φ'
  rcases hinl with h1 | h1 | h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = order48_K8_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = order48_K8_chi_02 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = order48_K8_chi_f0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = order48_K8_chi_f2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e.trans order48_K8_iso_f0_f2.some.symm⟩
  · have hχ : χ = order48_K8_chi_s0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = order48_K8_chi_s2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr
      ⟨e.trans order48_K8_iso_s2_p2.some |>.trans order48_K8_iso_p0_p2.some.symm |>.trans
        order48_K8_iso_s0_p0.some.symm⟩
  · have hχ : χ = order48_K8_chi_p0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr ⟨e.trans order48_K8_iso_s0_p0.some.symm⟩
  · have hχ : χ = order48_K8_chi_p2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr
      ⟨e.trans order48_K8_iso_p0_p2.some.symm |>.trans order48_K8_iso_s0_p0.some.symm⟩

/-! ## `K₉ = K₈g ⋊[ψ₅] C₂`

The ψ₅-invariance constraint DOES bite: `ψ₅ g₄ = g₄ · g₂` forces `χ(g₂) = 1`,
ruling out `snd` and `prod` on the `K8g`-part. -/

/-- **Exhaustiveness for `K = K₈g ⋊[ψ₅] C₂` (`G₉`, action `ψ₅ : (x,y) ↦ (x, c(x)y)`).**  The
character on the `C₂`-generator of `K8g` must vanish, leaving `{1, fst}` on the `K8g`-part. -/
theorem order48_classify_G9 (φ' : order16_wild_G9 →* MulAut (Multiplicative (ZMod 3))) :
    ∃ χ : order16_wild_G9 →* (ZMod 3)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨
        χ.comp SemidirectProduct.inl = order48_chiC4C2_fst) ∧
      (χ.comp SemidirectProduct.inr = 1 ∨ χ.comp SemidirectProduct.inr = order48_signC2) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G9 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G9 (order48_action χ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  refine ⟨ψ, ?_, c2_zmod3_character_cases _, ⟨semidirectProductCongr_eq hψ⟩⟩
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
  rcases order48_c4c2_zmod3_character_cases (ψ.comp SemidirectProduct.inl) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso; rw [h, order48_chiC4C2_snd_g2] at hkey; exact absurd hkey (by decide)
  · exfalso; rw [h, order48_chiC4C2_prod_g2] at hkey; exact absurd hkey (by decide)

theorem order48_K9_chiC4C2_one_invariant :
    ∀ b, (1 : K8g →* (ZMod 3)ˣ).comp (c2Action_psi5 b).toMonoidHom = 1 :=
  fun _ => by ext; simp

theorem order48_K9_chiC4C2_fst_invariant :
    ∀ b, order48_chiC4C2_fst.comp (c2Action_psi5 b).toMonoidHom = order48_chiC4C2_fst := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi5 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi5 _ from
        by rw [c2Action_psi5_gen]] <;>
    decide

noncomputable abbrev order48_K9_chi_00 : order16_wild_G9 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 1
    (fun b => by rw [order48_K9_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K9_chi_02 : order16_wild_G9 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 order48_signC2
    (fun b => by rw [order48_K9_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K9_chi_t0 : order16_wild_G9 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_fst 1
    (fun b => by rw [order48_K9_chiC4C2_fst_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K9_chi_t2 : order16_wild_G9 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_fst order48_signC2
    (fun b => by rw [order48_K9_chiC4C2_fst_invariant, mulAut_conj_of_comm]; ext a; simp)

/-- The `inl`/`inr`-MIXING automorphism `σ₃ : A ↦ AH, B ↦ B, H ↦ H` of `K₉` (with
`A = inl(1,0)`, `B = inl(0,1)`, `H = inr(1)`): well-defined since `AH` still has order `4`
(`(AH)² = A²B`) and `H(AH)H⁻¹ = (AH)·B = σ₃(A·B)`. On coordinates it is
`(a, b, h) ↦ (a, b + ⌊a/2⌋, h + (a mod 2))`. It merges `chi_02` with `chi_t2`
(`chi_02 ∘ σ₃ = chi_t2`). -/
noncomputable def order48_K9_sigma3 : order16_wild_G9 →* order16_wild_G9 :=
  MonoidHom.mk'
    (fun p =>
      ⟨(p.left.1,
        p.left.2 * Multiplicative.ofAdd
          (if Multiplicative.toAdd p.left.1 = 2 ∨ Multiplicative.toAdd p.left.1 = 3
            then (1 : ZMod 2) else 0)),
        p.right * Multiplicative.ofAdd
          (ZMod.castHom (by norm_num) (ZMod 2) (Multiplicative.toAdd p.left.1))⟩)
    (by decide)

theorem order48_K9_sigma3_bijective : Function.Bijective order48_K9_sigma3 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def order48_K9_sigma3_equiv : order16_wild_G9 ≃* order16_wild_G9 :=
  MulEquiv.ofBijective order48_K9_sigma3 order48_K9_sigma3_bijective

theorem order48_K9_chi_02_comp_sigma3 :
    order48_K9_chi_02.comp order48_K9_sigma3_equiv.toMonoidHom = order48_K9_chi_t2 := by
  apply MonoidHom.ext; decide

theorem order48_K9_iso_02_t2 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G9 (order48_action order48_K9_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G9
      (order48_action order48_K9_chi_t2)) :=
  order48_semidirectProduct_of_comp_eq order48_K9_sigma3_equiv order48_K9_chi_02_comp_sigma3

/-- **`K₉` contributes exactly `3` isomorphism classes**: representatives `order48_K9_chi_00`,
`order48_K9_chi_02` (`= chi_t2`, merged via the mixing automorphism `order48_K9_sigma3`), and
`order48_K9_chi_t0`. -/
theorem order48_classify_K9_reduced (φ' : order16_wild_G9 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G9 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G9
          (order48_action order48_K9_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G9 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G9
          (order48_action order48_K9_chi_02)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G9 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G9
          (order48_action order48_K9_chi_t0)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order48_classify_G9 φ'
  rcases hinl with h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = order48_K9_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = order48_K9_chi_02 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = order48_K9_chi_t0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = order48_K9_chi_t2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e.trans order48_K9_iso_02_t2.some.symm⟩

/-! ## `K₁₀ = K₈g ⋊[ψ₆] C₂ = Q₈ ⋊ C₂` (the Pauli group `C₄ ∘ D₄`)

As for `K₈`, ψ₆ inverts the `C₄`-generator, so the invariance constraint is automatic
for `±1`-valued characters and all four `K8g`-characters occur. -/

/-- **Exhaustiveness for `K = Q₈ ⋊ C₂` (`G₁₀`, action `ψ₆`).**  No constraint arises for
`±1`-valued characters (the same `χ(g₄)² = 1` constraint as `G₈`, here automatic). -/
theorem order48_classify_G10 (φ' : order16_wild_G10 →* MulAut (Multiplicative (ZMod 3))) :
    ∃ χ : order16_wild_G10 →* (ZMod 3)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨
        χ.comp SemidirectProduct.inl = order48_chiC4C2_fst ∨
        χ.comp SemidirectProduct.inl = order48_chiC4C2_snd ∨
        χ.comp SemidirectProduct.inl = order48_chiC4C2_prod) ∧
      (χ.comp SemidirectProduct.inr = 1 ∨ χ.comp SemidirectProduct.inr = order48_signC2) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10 (order48_action χ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, order48_c4c2_zmod3_character_cases _, c2_zmod3_character_cases _,
    ⟨semidirectProductCongr_eq hψ⟩⟩

theorem order48_K10_chiC4C2_one_invariant :
    ∀ b, (1 : K8g →* (ZMod 3)ˣ).comp (c2Action_psi6 b).toMonoidHom = 1 :=
  fun _ => by ext; simp

theorem order48_K10_chiC4C2_fst_invariant :
    ∀ b, order48_chiC4C2_fst.comp (c2Action_psi6 b).toMonoidHom = order48_chiC4C2_fst := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi6 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi6 _ from
        by rw [c2Action_psi6_gen]] <;>
    decide

theorem order48_K10_chiC4C2_snd_invariant :
    ∀ b, order48_chiC4C2_snd.comp (c2Action_psi6 b).toMonoidHom = order48_chiC4C2_snd := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi6 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi6 _ from
        by rw [c2Action_psi6_gen]] <;>
    decide

theorem order48_K10_chiC4C2_prod_invariant :
    ∀ b, order48_chiC4C2_prod.comp (c2Action_psi6 b).toMonoidHom = order48_chiC4C2_prod := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi6 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi6 _ from
        by rw [c2Action_psi6_gen]] <;>
    decide

noncomputable abbrev order48_K10_chi_00 : order16_wild_G10 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 1
    (fun b => by rw [order48_K10_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K10_chi_02 : order16_wild_G10 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 order48_signC2
    (fun b => by rw [order48_K10_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K10_chi_f0 : order16_wild_G10 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_fst 1
    (fun b => by rw [order48_K10_chiC4C2_fst_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K10_chi_f2 : order16_wild_G10 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_fst order48_signC2
    (fun b => by rw [order48_K10_chiC4C2_fst_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K10_chi_s0 : order16_wild_G10 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_snd 1
    (fun b => by rw [order48_K10_chiC4C2_snd_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K10_chi_s2 : order16_wild_G10 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_snd order48_signC2
    (fun b => by rw [order48_K10_chiC4C2_snd_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K10_chi_p0 : order16_wild_G10 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_prod 1
    (fun b => by rw [order48_K10_chiC4C2_prod_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K10_chi_p2 : order16_wild_G10 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_chiC4C2_prod order48_signC2
    (fun b => by rw [order48_K10_chiC4C2_prod_invariant, mulAut_conj_of_comm]; ext a; simp)

/-- Outer shear `s ↦ s·k` for `k = inl(1,0)·inr(1)`, toggling the outer `C₂`-character for the
`fst`/`prod` families: merges `f0 = f2` and `p0 = p2`. -/
noncomputable def order48_K10_shearOuter_B : order16_wild_G10 :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 2))) *
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem order48_K10_shearOuter_B_pow2 : order48_K10_shearOuter_B ^ 2 = 1 := by decide

theorem order48_K10_shearOuter_compat :
    ∀ b, (SemidirectProduct.inl : K8g →* order16_wild_G10).comp (c2Action_psi6 b).toMonoidHom =
      (MulAut.conj ((C2_powHom order48_K10_shearOuter_B order48_K10_shearOuter_B_pow2) b)
        ).toMonoidHom.comp (SemidirectProduct.inl : K8g →* order16_wild_G10) := by
  intro b
  apply MonoidHom.ext
  intro a
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · simp
  · change SemidirectProduct.inl (psi6 a) =
      MulAut.conj (order48_K10_shearOuter_B) (SemidirectProduct.inl a)
    rw [MulAut.conj_apply, order48_K10_shearOuter_B]
    revert a; decide

noncomputable def order48_K10_shearOuter : order16_wild_G10 →* order16_wild_G10 :=
  SemidirectProduct.lift (SemidirectProduct.inl : K8g →* order16_wild_G10)
    (C2_powHom order48_K10_shearOuter_B order48_K10_shearOuter_B_pow2)
    order48_K10_shearOuter_compat

theorem order48_K10_shearOuter_bijective : Function.Bijective order48_K10_shearOuter := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def order48_K10_shearOuter_equiv : order16_wild_G10 ≃* order16_wild_G10 :=
  MulEquiv.ofBijective order48_K10_shearOuter order48_K10_shearOuter_bijective

theorem order48_K10_chi_f0_comp_shearOuter :
    order48_K10_chi_f0.comp order48_K10_shearOuter_equiv.toMonoidHom = order48_K10_chi_f2 := by
  apply MonoidHom.ext; decide
theorem order48_K10_chi_p0_comp_shearOuter :
    order48_K10_chi_p0.comp order48_K10_shearOuter_equiv.toMonoidHom = order48_K10_chi_p2 := by
  apply MonoidHom.ext; decide

theorem order48_K10_iso_f0_f2 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G10 (order48_action order48_K10_chi_f0) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
      (order48_action order48_K10_chi_f2)) :=
  order48_semidirectProduct_of_comp_eq order48_K10_shearOuter_equiv
    order48_K10_chi_f0_comp_shearOuter
theorem order48_K10_iso_p0_p2 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G10 (order48_action order48_K10_chi_p0) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
      (order48_action order48_K10_chi_p2)) :=
  order48_semidirectProduct_of_comp_eq order48_K10_shearOuter_equiv
    order48_K10_chi_p0_comp_shearOuter

/-- An `inl`/`inr`-MIXING automorphism of `K₁₀` (the Pauli group, center `⟨AB⟩ ≅ C₄`):
`σ₁ : A ↦ ABH, B ↦ H, H ↦ B` (with `A = inl(1,0)`, `B = inl(0,1)`, `H = inr(1)`). On
coordinates: `(a, b, h) ↦ (a + 2h(ā+b), ā+h, ā+b)` with `ā = a mod 2`. It merges `chi_02`
with `chi_p0`. -/
noncomputable def order48_K10_sigma1 : order16_wild_G10 →* order16_wild_G10 :=
  MonoidHom.mk'
    (fun p =>
      ⟨(p.left.1 * Multiplicative.ofAdd
          (if Multiplicative.toAdd p.right = 1 ∧
              ZMod.castHom (by norm_num) (ZMod 2) (Multiplicative.toAdd p.left.1) +
                Multiplicative.toAdd p.left.2 = 1
            then (2 : ZMod 4) else 0),
        Multiplicative.ofAdd
          (ZMod.castHom (by norm_num) (ZMod 2) (Multiplicative.toAdd p.left.1) +
            Multiplicative.toAdd p.right)),
        Multiplicative.ofAdd
          (ZMod.castHom (by norm_num) (ZMod 2) (Multiplicative.toAdd p.left.1) +
            Multiplicative.toAdd p.left.2)⟩)
    (by decide)

theorem order48_K10_sigma1_bijective : Function.Bijective order48_K10_sigma1 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def order48_K10_sigma1_equiv : order16_wild_G10 ≃* order16_wild_G10 :=
  MulEquiv.ofBijective order48_K10_sigma1 order48_K10_sigma1_bijective

theorem order48_K10_chi_02_comp_sigma1 :
    order48_K10_chi_02.comp order48_K10_sigma1_equiv.toMonoidHom = order48_K10_chi_p0 := by
  apply MonoidHom.ext; decide

theorem order48_K10_iso_02_p0 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G10 (order48_action order48_K10_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
      (order48_action order48_K10_chi_p0)) :=
  order48_semidirectProduct_of_comp_eq order48_K10_sigma1_equiv order48_K10_chi_02_comp_sigma1

/-- A second `inl`/`inr`-MIXING automorphism of `K₁₀`: `σ₂ : A ↦ BH, B ↦ AH, H ↦ B`. On
coordinates: `(a, b, h) ↦ (a − ā + (−1)^ā·b + 2h(ā+b), ā+h, ā+b)`. It merges `chi_f0` with
`chi_s0`. -/
noncomputable def order48_K10_sigma2 : order16_wild_G10 →* order16_wild_G10 :=
  MonoidHom.mk'
    (fun p =>
      ⟨(Multiplicative.ofAdd
          ((if Multiplicative.toAdd p.left.1 = 2 ∨ Multiplicative.toAdd p.left.1 = 3
              then (2 : ZMod 4) else 0) +
            (if Multiplicative.toAdd p.left.2 = 1
              then (if Multiplicative.toAdd p.left.1 = 1 ∨ Multiplicative.toAdd p.left.1 = 3
                then (3 : ZMod 4) else 1) else 0) +
            (if Multiplicative.toAdd p.right = 1 ∧
                ZMod.castHom (by norm_num) (ZMod 2) (Multiplicative.toAdd p.left.1) +
                  Multiplicative.toAdd p.left.2 = 1
              then (2 : ZMod 4) else 0)),
        Multiplicative.ofAdd
          (ZMod.castHom (by norm_num) (ZMod 2) (Multiplicative.toAdd p.left.1) +
            Multiplicative.toAdd p.right)),
        Multiplicative.ofAdd
          (ZMod.castHom (by norm_num) (ZMod 2) (Multiplicative.toAdd p.left.1) +
            Multiplicative.toAdd p.left.2)⟩)
    (by decide)

theorem order48_K10_sigma2_bijective : Function.Bijective order48_K10_sigma2 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def order48_K10_sigma2_equiv : order16_wild_G10 ≃* order16_wild_G10 :=
  MulEquiv.ofBijective order48_K10_sigma2 order48_K10_sigma2_bijective

theorem order48_K10_chi_f0_comp_sigma2 :
    order48_K10_chi_f0.comp order48_K10_sigma2_equiv.toMonoidHom = order48_K10_chi_s0 := by
  apply MonoidHom.ext; decide

theorem order48_K10_iso_f0_s0 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G10 (order48_action order48_K10_chi_f0) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
      (order48_action order48_K10_chi_s0)) :=
  order48_semidirectProduct_of_comp_eq order48_K10_sigma2_equiv order48_K10_chi_f0_comp_sigma2

/-- **`K₁₀` (the Pauli group `C₄ ∘ D₄`) contributes exactly `4` isomorphism classes**: the
`Aut(K₁₀)`-orbits of the `8` raw characters, organised by the (invariant) value at the
central generator `AB`: value `+1` gives `{00}` and `{02 = p0 = p2}` (merged via
`order48_K10_sigma1` and `order48_K10_shearOuter`); value `−1` gives `{f0 = f2 = s0}`
(merged via `order48_K10_shearOuter` and `order48_K10_sigma2`; kernels `≅ D₈`) and the
fixed point `{s2}` (kernel `≅ Q₈`). Representatives: `order48_K10_chi_00`,
`order48_K10_chi_02`, `order48_K10_chi_f0`, `order48_K10_chi_s2`. -/
theorem order48_classify_K10_reduced (φ' : order16_wild_G10 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
          (order48_action order48_K10_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
          (order48_action order48_K10_chi_02)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
          (order48_action order48_K10_chi_f0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G10
          (order48_action order48_K10_chi_s2)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order48_classify_G10 φ'
  rcases hinl with h1 | h1 | h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = order48_K10_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = order48_K10_chi_02 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = order48_K10_chi_f0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = order48_K10_chi_f2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e.trans order48_K10_iso_f0_f2.some.symm⟩
  · have hχ : χ = order48_K10_chi_s0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e.trans order48_K10_iso_f0_s0.some.symm⟩
  · have hχ : χ = order48_K10_chi_s2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = order48_K10_chi_p0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e.trans order48_K10_iso_02_p0.some.symm⟩
  · have hχ : χ = order48_K10_chi_p2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl
      ⟨e.trans order48_K10_iso_p0_p2.some.symm |>.trans order48_K10_iso_02_p0.some.symm⟩

/-! ## `K₁₁ = Q₈ × C₂` (direct product) -/

/-- **Exhaustiveness for `K = Q₈ × C₂` (`G₁₁`).**  No constraint links the factors. -/
theorem order48_classify_G11 (φ' : order16_wild_G11 →* MulAut (Multiplicative (ZMod 3))) :
    ∃ χ : order16_wild_G11 →* (ZMod 3)ˣ,
      (χ.comp (MonoidHom.inl _ _) = 1 ∨ χ.comp (MonoidHom.inl _ _) = order48_chiQ8 ∨
        χ.comp (MonoidHom.inl _ _) = order48_chiQ8_xa ∨
        χ.comp (MonoidHom.inl _ _) = order48_chiQ8_prod) ∧
      (χ.comp (MonoidHom.inr _ _) = 1 ∨ χ.comp (MonoidHom.inr _ _) = order48_signC2) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11 (order48_action χ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, order48_q8_zmod3_character_cases _, c2_zmod3_character_cases _,
    ⟨semidirectProductCongr_eq hψ⟩⟩

noncomputable abbrev order48_K11_chi_00 : order16_wild_G11 →* (ZMod 3)ˣ :=
  (1 : QuaternionGroup 2 →* (ZMod 3)ˣ).coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)
noncomputable abbrev order48_K11_chi_10 : order16_wild_G11 →* (ZMod 3)ˣ :=
  order48_chiQ8.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)
noncomputable abbrev order48_K11_chi_20 : order16_wild_G11 →* (ZMod 3)ˣ :=
  order48_chiQ8_xa.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)
noncomputable abbrev order48_K11_chi_30 : order16_wild_G11 →* (ZMod 3)ˣ :=
  order48_chiQ8_prod.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)
noncomputable abbrev order48_K11_chi_02 : order16_wild_G11 →* (ZMod 3)ˣ :=
  (1 : QuaternionGroup 2 →* (ZMod 3)ˣ).coprod order48_signC2
noncomputable abbrev order48_K11_chi_12 : order16_wild_G11 →* (ZMod 3)ˣ :=
  order48_chiQ8.coprod order48_signC2
noncomputable abbrev order48_K11_chi_22 : order16_wild_G11 →* (ZMod 3)ˣ :=
  order48_chiQ8_xa.coprod order48_signC2
noncomputable abbrev order48_K11_chi_32 : order16_wild_G11 →* (ZMod 3)ˣ :=
  order48_chiQ8_prod.coprod order48_signC2

/-- `Aut(Q₈)`-orbit moves (from `Order88.lean`), extended by the identity on `C₂`, merging
the `3` nontrivial `Q₈`-part-only characters `chi_10, chi_20, chi_30`. -/
noncomputable def order48_K11_shear : order16_wild_G11 ≃* order16_wild_G11 :=
  MulEquiv.prodCongr order88_Q8_shear (MulEquiv.refl _)
noncomputable def order48_K11_swap : order16_wild_G11 ≃* order16_wild_G11 :=
  MulEquiv.prodCongr order88_Q8_swap (MulEquiv.refl _)

theorem order48_K11_chi_10_comp_shear :
    order48_K11_chi_10.comp order48_K11_shear.toMonoidHom = order48_K11_chi_30 := by
  apply MonoidHom.ext; decide
theorem order48_K11_chi_10_comp_swap :
    order48_K11_chi_10.comp order48_K11_swap.toMonoidHom = order48_K11_chi_20 := by
  apply MonoidHom.ext; decide

theorem order48_K11_iso_10_30 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G11 (order48_action order48_K11_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11
      (order48_action order48_K11_chi_30)) :=
  order48_semidirectProduct_of_comp_eq order48_K11_shear order48_K11_chi_10_comp_shear
theorem order48_K11_iso_10_20 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G11 (order48_action order48_K11_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11
      (order48_action order48_K11_chi_20)) :=
  order48_semidirectProduct_of_comp_eq order48_K11_swap order48_K11_chi_10_comp_swap

theorem order48_c2_sq_one (y : Multiplicative (ZMod 2)) : y ^ 2 = 1 := by revert y; decide

/-- **The `Q₈`-abelianization shear**: `(q,c) ↦ (q, c · f(q))` for `f : Q₈ → C₂` a
homomorphism. Merges `chi_02` (`C₂`-part alone nontrivial) with `chi_x2` for any nontrivial
`Q₈`-part `x`, since `C₂`'s dual character detects the shift `f(q)` as exactly the
corresponding `Q₈`-character. -/
noncomputable def order48_K11_shearC2 (f : QuaternionGroup 2 →* Multiplicative (ZMod 2)) :
    order16_wild_G11 ≃* order16_wild_G11 where
  toFun p := (p.1, p.2 * f p.1)
  invFun p := (p.1, p.2 * f p.1)
  left_inv p := by
    have hf : f p.1 * f p.1 = 1 := by rw [← sq]; exact order48_c2_sq_one _
    ext
    · rfl
    · change p.2 * f p.1 * f p.1 = p.2
      rw [mul_assoc, hf, mul_one]
  right_inv p := by
    have hf : f p.1 * f p.1 = 1 := by rw [← sq]; exact order48_c2_sq_one _
    ext
    · rfl
    · change p.2 * f p.1 * f p.1 = p.2
      rw [mul_assoc, hf, mul_one]
  map_mul' p q := by
    ext
    · rfl
    · change p.2 * q.2 * f (p.1 * q.1) = p.2 * f p.1 * (q.2 * f q.1)
      rw [map_mul]
      rw [show p.2 * f p.1 * (q.2 * f q.1) = p.2 * q.2 * (f p.1 * f q.1) from by
        rw [mul_assoc, mul_assoc]; congr 1; rw [← mul_assoc, ← mul_assoc, mul_comm (f p.1) q.2]]

theorem order48_K11_chi_02_comp_shearC2_chiQ8 :
    order48_K11_chi_02.comp (order48_K11_shearC2 order88_chiQ8).toMonoidHom =
      order48_K11_chi_12 := by
  apply MonoidHom.ext; decide
theorem order48_K11_chi_02_comp_shearC2_chiQ8_xa :
    order48_K11_chi_02.comp (order48_K11_shearC2 order88_chiQ8_xa).toMonoidHom =
      order48_K11_chi_22 := by
  apply MonoidHom.ext; decide
theorem order48_K11_chi_02_comp_shearC2_chiQ8_prod :
    order48_K11_chi_02.comp (order48_K11_shearC2 order88_chiQ8_prod).toMonoidHom =
      order48_K11_chi_32 := by
  apply MonoidHom.ext; decide

theorem order48_K11_iso_02_12 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G11 (order48_action order48_K11_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11
      (order48_action order48_K11_chi_12)) :=
  order48_semidirectProduct_of_comp_eq (order48_K11_shearC2 order88_chiQ8)
    order48_K11_chi_02_comp_shearC2_chiQ8
theorem order48_K11_iso_02_22 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G11 (order48_action order48_K11_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11
      (order48_action order48_K11_chi_22)) :=
  order48_semidirectProduct_of_comp_eq (order48_K11_shearC2 order88_chiQ8_xa)
    order48_K11_chi_02_comp_shearC2_chiQ8_xa
theorem order48_K11_iso_02_32 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G11 (order48_action order48_K11_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11
      (order48_action order48_K11_chi_32)) :=
  order48_semidirectProduct_of_comp_eq (order48_K11_shearC2 order88_chiQ8_prod)
    order48_K11_chi_02_comp_shearC2_chiQ8_prod

/-- **`K₁₁ = Q₈ × C₂` contributes exactly `3` isomorphism classes**: the `8` raw candidates
collapse to `order48_K11_chi_00` (trivial), `order48_K11_chi_10` (`= chi_20 = chi_30`,
`Q₈`-part alone nontrivial, merged via `Aut(Q₈) ≅ S₄`'s transitive action on the `3`
nontrivial `Q₈ → C₂` characters), and `order48_K11_chi_02` (`= chi_12 = chi_22 = chi_32`,
ANY character with nontrivial `C₂`-part, merged via the abelianization shear
`order48_K11_shearC2`). -/
theorem order48_classify_K11_reduced (φ' : order16_wild_G11 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11
          (order48_action order48_K11_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11
          (order48_action order48_K11_chi_10)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G11
          (order48_action order48_K11_chi_02)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order48_classify_G11 φ'
  rcases hinl with h1 | h1 | h1 | h1 <;> rcases hinr with h2 | h2 <;>
    rw [show χ = (χ.comp (MonoidHom.inl _ _)).coprod (χ.comp (MonoidHom.inr _ _)) from
      (MonoidHom.coprod_unique χ).symm, h1, h2] at e
  · exact Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr ⟨e⟩
  · exact Or.inr <| Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr ⟨e.trans order48_K11_iso_02_12.some.symm⟩
  · exact Or.inr <| Or.inl ⟨e.trans order48_K11_iso_10_20.some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans order48_K11_iso_02_22.some.symm⟩
  · exact Or.inr <| Or.inl ⟨e.trans order48_K11_iso_10_30.some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans order48_K11_iso_02_32.some.symm⟩

/-! ## `K₁₂ = C₄ ⋊ C₄` (`order16_N3`, inversion action `x ↦ x³`)

The invariance constraint `χ(a)³ = χ(a)` on the normal `C₄`-factor is automatic for
`±1`-valued characters, so both factors carry an independent sign. -/

/-- **Exhaustiveness for `K = C₄ ⋊ C₄` (`G₁₂`, inversion action).** -/
theorem order48_classify_G12 (φ' : order16_wild_G12 →* MulAut (Multiplicative (ZMod 3))) :
    ∃ χ : order16_wild_G12 →* (ZMod 3)ˣ,
      (χ.comp SemidirectProduct.inl = 1 ∨ χ.comp SemidirectProduct.inl = order48_signC4) ∧
      (χ.comp SemidirectProduct.inr = 1 ∨ χ.comp SemidirectProduct.inr = order48_signC4) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G12 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G12 (order48_action χ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, c4_zmod3_character_cases _, c4_zmod3_character_cases _,
    ⟨semidirectProductCongr_eq hψ⟩⟩

theorem order48_K12_chi_one_invariant :
    ∀ b, (1 : Multiplicative (ZMod 4) →* (ZMod 3)ˣ).comp
      (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 b).toMonoidHom = 1 :=
  fun _ => by ext; simp

/-- `order48_signC4` is invariant under the inversion action (`(-1)³ = -1`). -/
theorem order48_K12_signC4_invariant :
    ∀ b, order48_signC4.comp (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 b).toMonoidHom =
      order48_signC4 := by
  intro b
  apply c4_hom_ext
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 4) ∨
      b = (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ∨ b = (Multiplicative.ofAdd (1 : ZMod 4)) ^ 3 :=
    by revert b; decide
  rcases hb with rfl | rfl | rfl | rfl
  · simp
  · rw [c4ActionAut3_gen, map_pow]; decide
  · have h : (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4)
        ((Multiplicative.ofAdd (1 : ZMod 4)) ^ 2) = 1 := by
      ext x; revert x; decide
    rw [h]; simp
  · have h : (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4)
        ((Multiplicative.ofAdd (1 : ZMod 4)) ^ 3) =
        c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 (Multiplicative.ofAdd (1 : ZMod 4)) := by
      ext x; revert x; decide
    rw [h, c4ActionAut3_gen, map_pow]
    decide

noncomputable abbrev order48_K12_chi_00 : order16_wild_G12 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 1
    (fun b => by rw [order48_K12_chi_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K12_chi_02 : order16_wild_G12 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 order48_signC4
    (fun b => by rw [order48_K12_chi_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K12_chi_20 : order16_wild_G12 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_signC4 1
    (fun b => by rw [order48_K12_signC4_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev order48_K12_chi_22 : order16_wild_G12 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_signC4 order48_signC4
    (fun b => by rw [order48_K12_signC4_invariant, mulAut_conj_of_comm]; ext a; simp)

/-- The shear `σ₁ : a ↦ a, b ↦ ab` of `K₁₂ = C₄ ⋊ C₄` (valid since `(ab)² = b²`, so `ab` has
order `4` and still inverts `a` under conjugation). On coordinates: `(i, j) ↦ (i + (j mod 2), j)`.
Merges `chi_20` with `chi_22`. -/
noncomputable def order48_K12_sigma1 : order16_wild_G12 →* order16_wild_G12 :=
  MonoidHom.mk'
    (fun p =>
      ⟨p.left * Multiplicative.ofAdd
          (if Multiplicative.toAdd p.right = 1 ∨ Multiplicative.toAdd p.right = 3
            then (1 : ZMod 4) else 0),
        p.right⟩)
    (by decide)

theorem order48_K12_sigma1_bijective : Function.Bijective order48_K12_sigma1 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def order48_K12_sigma1_equiv : order16_wild_G12 ≃* order16_wild_G12 :=
  MulEquiv.ofBijective order48_K12_sigma1 order48_K12_sigma1_bijective

theorem order48_K12_chi_20_comp_sigma1 :
    order48_K12_chi_20.comp order48_K12_sigma1_equiv.toMonoidHom = order48_K12_chi_22 := by
  apply MonoidHom.ext; decide

theorem order48_K12_iso_20_22 : Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
    order16_wild_G12 (order48_action order48_K12_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G12
      (order48_action order48_K12_chi_22)) :=
  order48_semidirectProduct_of_comp_eq order48_K12_sigma1_equiv order48_K12_chi_20_comp_sigma1

/-- **`K₁₂ = C₄ ⋊ C₄` contributes exactly `3` isomorphism classes**: the `Aut(K₁₂)`-orbits of
the `4` raw characters are `{00}` (trivial), `{02}` (`χ(a) = 1`, `χ(b) = −1`, kernel
`⟨a, b²⟩`), and `{20 = 22}` (`χ(a) = −1`, merged via the shear `order48_K12_sigma1`
`a ↦ a, b ↦ ab`). -/
theorem order48_classify_K12_reduced (φ' : order16_wild_G12 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G12 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G12
          (order48_action order48_K12_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G12 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G12
          (order48_action order48_K12_chi_02)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G12 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G12
          (order48_action order48_K12_chi_20)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order48_classify_G12 φ'
  rcases hinl with h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = order48_K12_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = order48_K12_chi_02 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = order48_K12_chi_20 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = order48_K12_chi_22 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr ⟨e.trans order48_K12_iso_20_22.some.symm⟩

end Smallgroups.UsefulTheorems
