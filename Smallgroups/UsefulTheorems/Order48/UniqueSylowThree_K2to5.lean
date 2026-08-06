/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.UniqueSylowThree

/-!
# Isomorphism classes of `C₃ ⋊ Kᵢ` for `i = 2, 3, 4, 5`

`Order48/UniqueSylowThree.lean` narrows any action `φ' : Kᵢ →* MulAut C₃` (with
`K₂ = SD₁₆`, `K₃ = M₁₆`, `K₄ = D₁₆` the `C₈`-semidirect family and `K₅ = Q₁₆`)
to a character `χ : Kᵢ →* (ZMod 3)ˣ` whose values on the `C₈`- and `C₂`-parts
are each `1` or `−1` (`order48_classify_G2/G3/G4`).  Since `(ZMod 3)ˣ` is
abelian, conjugation on `MulAut C₃` is trivial, so two candidate characters
give isomorphic semidirect products iff they lie in the same `Aut(Kᵢ)`-orbit
(under precomposition, via `order48_semidirectProduct_of_comp_eq`).

This file builds the four raw candidates per kernel via
`SemidirectProduct.lift`, computes the orbit structure, and packages the
"reduced" exhaustiveness theorems:

* `K₂ = SD₁₆`: **4 classes, no merges** (the three index-`2` subgroups `C₈`,
  `D₈`, `Q₈` of `SD₁₆` are all characteristic) — `order48_classify_K2_reduced`;
* `K₃ = M₁₆`: **3 classes** — `chi_01 ~ chi_11` merge via the automorphism
  `τ : a ↦ a·b, b ↦ b` (`order48_K3_tau_equiv`) — `order48_classify_K3_reduced`;
* `K₄ = D₁₆`: **3 classes** — `chi_10 ~ chi_11` merge via the automorphism
  `σ : a ↦ a, b ↦ a·b` (`order48_K4_sigma_equiv`) — `order48_classify_K4_reduced`;
* `K₅ = Q₁₆`: **3 classes** — the character `χ(a) = −1, χ(b) = −1` merges into
  `χ(a) = −1, χ(b) = 1` via `σ : a ↦ a, b ↦ a·b` (`order48_K5_sigma`) —
  `order48_classify_K5_reduced`.
-/

namespace Smallgroups.UsefulTheorems

/-! ## General helpers -/

/-- Conjugation by any element of an abelian group is trivial. -/
theorem order48_mulAut_conj_of_comm {M : Type*} [CommGroup M] (m : M) : MulAut.conj m = 1 := by
  ext x
  simp [MulAut.conj_apply]

/-- Every unit of `ZMod 3` squares to `1`. -/
theorem order48_zmod3_unit_sq (u : (ZMod 3)ˣ) : u ^ 2 = 1 := by revert u; decide

/-- `SemidirectProduct.lift`'s composite with `inl` recovers the first component. -/
theorem order48_lift_comp_inl {A B M : Type*} [Group A] [Group B] [CommGroup M]
    {φ : B →* MulAut A} (f1 : A →* M) (f2 : B →* M)
    (h : ∀ b, f1.comp (φ b).toMonoidHom = (MulAut.conj (f2 b)).toMonoidHom.comp f1) :
    (SemidirectProduct.lift f1 f2 h).comp SemidirectProduct.inl = f1 :=
  SemidirectProduct.lift_comp_inl f1 f2 h

/-- `SemidirectProduct.lift`'s composite with `inr` recovers the second component. -/
theorem order48_lift_comp_inr {A B M : Type*} [Group A] [Group B] [CommGroup M]
    {φ : B →* MulAut A} (f1 : A →* M) (f2 : B →* M)
    (h : ∀ b, f1.comp (φ b).toMonoidHom = (MulAut.conj (f2 b)).toMonoidHom.comp f1) :
    (SemidirectProduct.lift f1 f2 h).comp SemidirectProduct.inr = f2 :=
  SemidirectProduct.lift_comp_inr f1 f2 h

/-- A hom out of `C₈` into any group, sending the generator to a chosen
order-dividing-`8` element. -/
noncomputable def order48_C8_powHom {G : Type*} [Group G] (A : G) (hA : A ^ 8 = 1) :
    Multiplicative (ZMod 8) →* G :=
  MonoidHom.mk' (fun x => A ^ (Multiplicative.toAdd x).val) (by
    intro x y
    change A ^ (Multiplicative.toAdd (x * y)).val =
      A ^ (Multiplicative.toAdd x).val * A ^ (Multiplicative.toAdd y).val
    rw [← pow_add]
    have hval : (Multiplicative.toAdd (x * y)).val =
        ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) % 8 := by
      change (Multiplicative.toAdd x + Multiplicative.toAdd y).val = _
      rw [ZMod.val_add]
    rw [hval, ← Nat.div_add_mod ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) 8,
      pow_add, pow_mul, hA, one_pow, one_mul]
    congr 1
    omega)

/-- A hom out of `C₂` into any group, sending the generator to a chosen
order-dividing-`2` element. -/
noncomputable def order48_C2_powHom {G : Type*} [Group G] (B : G) (hB : B ^ 2 = 1) :
    Multiplicative (ZMod 2) →* G :=
  MonoidHom.mk' (fun x => B ^ (Multiplicative.toAdd x).val) (by
    intro x y
    change B ^ (Multiplicative.toAdd (x * y)).val =
      B ^ (Multiplicative.toAdd x).val * B ^ (Multiplicative.toAdd y).val
    rw [← pow_add]
    have hval : (Multiplicative.toAdd (x * y)).val =
        ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) % 2 := by
      change (Multiplicative.toAdd x + Multiplicative.toAdd y).val = _
      rw [ZMod.val_add]
    rw [hval, ← Nat.div_add_mod ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) 2,
      pow_add, pow_mul, hB, one_pow, one_mul]
    congr 1
    omega)

/-! ### Lift-compatibility for the three `C₈ ⋊ C₂` actions

Every `±1`-valued character `f1 : C₈ →* (ZMod 3)ˣ` is invariant under
`φ₂ : x ↦ x³`, `φ₃ : x ↦ x⁵` and `φ₄ : x ↦ x⁷`, because the exponents are odd
and `u² = 1` for all `u ∈ (ZMod 3)ˣ`.  Hence any pair `(f1, f2)` lifts to a
character of the semidirect kernel. -/

theorem order48_K2_lift_compat (f1 : C8g →* (ZMod 3)ˣ)
    (f2 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ) :
    ∀ b, f1.comp (c2Action_phi2 b).toMonoidHom =
      (MulAut.conj (f2 b)).toMonoidHom.comp f1 := by
  intro b
  rw [order48_mulAut_conj_of_comm]
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · rfl
  · apply multiplicative_zmod_hom_ext
    change f1 (c2Action_phi2 (Multiplicative.ofAdd (1 : ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8))) = f1 (Multiplicative.ofAdd (1 : ZMod 8))
    rw [show c2Action_phi2 (Multiplicative.ofAdd (1 : ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8)) = phi2 (Multiplicative.ofAdd (1 : ZMod 8)) from by
        rw [c2Action_phi2_gen],
      phi2_gen, map_pow]
    rcases zmod3_unit_eq_one_or_neg (f1 (Multiplicative.ofAdd (1 : ZMod 8))) with h | h <;>
      rw [h] <;> decide

theorem order48_K3_lift_compat (f1 : C8g →* (ZMod 3)ˣ)
    (f2 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ) :
    ∀ b, f1.comp (c2Action_phi3 b).toMonoidHom =
      (MulAut.conj (f2 b)).toMonoidHom.comp f1 := by
  intro b
  rw [order48_mulAut_conj_of_comm]
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · rfl
  · apply multiplicative_zmod_hom_ext
    change f1 (c2Action_phi3 (Multiplicative.ofAdd (1 : ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8))) = f1 (Multiplicative.ofAdd (1 : ZMod 8))
    rw [show c2Action_phi3 (Multiplicative.ofAdd (1 : ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8)) = phi3 (Multiplicative.ofAdd (1 : ZMod 8)) from by
        rw [c2Action_phi3_gen],
      phi3_gen, map_pow]
    rcases zmod3_unit_eq_one_or_neg (f1 (Multiplicative.ofAdd (1 : ZMod 8))) with h | h <;>
      rw [h] <;> decide

theorem order48_K4_lift_compat (f1 : C8g →* (ZMod 3)ˣ)
    (f2 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ) :
    ∀ b, f1.comp (c2Action_phi4 b).toMonoidHom =
      (MulAut.conj (f2 b)).toMonoidHom.comp f1 := by
  intro b
  rw [order48_mulAut_conj_of_comm]
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · rfl
  · apply multiplicative_zmod_hom_ext
    change f1 (c2Action_phi4 (Multiplicative.ofAdd (1 : ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8))) = f1 (Multiplicative.ofAdd (1 : ZMod 8))
    rw [show c2Action_phi4 (Multiplicative.ofAdd (1 : ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8)) = phi4 (Multiplicative.ofAdd (1 : ZMod 8)) from by
        rw [c2Action_phi4_gen],
      phi4_gen, map_pow]
    rcases zmod3_unit_eq_one_or_neg (f1 (Multiplicative.ofAdd (1 : ZMod 8))) with h | h <;>
      rw [h] <;> decide

/-! ## `K₂ = SD₁₆ = C₈ ⋊₃ C₂`: the `4` raw candidates, no merges -/

/-- The four representative characters `SD₁₆ →* (ZMod 3)ˣ`, built via
`SemidirectProduct.lift` from the two `C₈`-characters (`1`, `order48_signC8`)
and the two `C₂`-characters (`1`, `order48_signC2`).  Subscripts: first digit
is the sign on the `C₈`-part, second digit the sign on the `C₂`-part. -/
noncomputable abbrev order48_K2_chi_00 : order16_wild_G2 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 1 (order48_K2_lift_compat 1 1)
noncomputable abbrev order48_K2_chi_10 : order16_wild_G2 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_signC8 1 (order48_K2_lift_compat _ _)
noncomputable abbrev order48_K2_chi_01 : order16_wild_G2 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 order48_signC2 (order48_K2_lift_compat _ _)
noncomputable abbrev order48_K2_chi_11 : order16_wild_G2 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_signC8 order48_signC2 (order48_K2_lift_compat _ _)

/-- **`K₂ = SD₁₆` contributes exactly `4` isomorphism classes**, with no merging:
the three index-`2` subgroups of `SD₁₆` (`C₈`, `D₈`, `Q₈`) are all
characteristic, so every character is its own `Aut(SD₁₆)`-orbit. -/
theorem order48_classify_K2_reduced (φ' : order16_wild_G2 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2
          (order48_action order48_K2_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2
          (order48_action order48_K2_chi_10)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2
          (order48_action order48_K2_chi_01)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G2
          (order48_action order48_K2_chi_11)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order48_classify_G2 φ'
  rcases hinl with h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = order48_K2_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = order48_K2_chi_01 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = order48_K2_chi_10 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = order48_K2_chi_11 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr ⟨e⟩

/-! ## `K₃ = M₁₆ = C₈ ⋊₅ C₂` (modular group): `4` raw candidates, one merge -/

noncomputable abbrev order48_K3_chi_00 : order16_wild_G3 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 1 (order48_K3_lift_compat 1 1)
noncomputable abbrev order48_K3_chi_10 : order16_wild_G3 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_signC8 1 (order48_K3_lift_compat _ _)
noncomputable abbrev order48_K3_chi_01 : order16_wild_G3 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 order48_signC2 (order48_K3_lift_compat _ _)
noncomputable abbrev order48_K3_chi_11 : order16_wild_G3 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_signC8 order48_signC2 (order48_K3_lift_compat _ _)

/-! ### The merge `chi_01 ~ chi_11`: the automorphism `τ : a ↦ a·b, b ↦ b` of `M₁₆`

`τ` respects the semidirect relation: `b·(a·b)·b⁻¹ = (a·b)⁵` since both sides
equal `a⁵b`; verified by `decide` inside `order48_K3_tau_compat`. -/

/-- The element `A = a·b ∈ M₁₆`: an order-`8` element generating the "other"
index-`2` cyclic subgroup. -/
noncomputable def order48_K3_A : order16_wild_G3 :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8)) *
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem order48_K3_A_pow8 : order48_K3_A ^ 8 = 1 := by decide

/-- `B = b`: the `C₂`-generator itself. -/
noncomputable def order48_K3_B : order16_wild_G3 :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem order48_K3_B_pow2 : order48_K3_B ^ 2 = 1 := by decide

/-- The compatibility condition for
`SemidirectProduct.lift (C8_powHom A) (C2_powHom B)`: `B` conjugates `A`
exactly as `b` conjugates `a` in the original presentation. -/
theorem order48_K3_tau_compat :
    ∀ b, (order48_C8_powHom order48_K3_A order48_K3_A_pow8).comp
        (c2Action_phi3 b).toMonoidHom =
      (MulAut.conj ((order48_C2_powHom order48_K3_B order48_K3_B_pow2) b)).toMonoidHom.comp
        (order48_C8_powHom order48_K3_A order48_K3_A_pow8) := by
  intro b
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · apply multiplicative_zmod_hom_ext
    change (order48_C8_powHom order48_K3_A order48_K3_A_pow8)
        (c2Action_phi3 (1 : Multiplicative (ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 8))) =
      (MulAut.conj ((order48_C2_powHom order48_K3_B order48_K3_B_pow2)
          (1 : Multiplicative (ZMod 2)))).toMonoidHom
        (order48_C8_powHom order48_K3_A order48_K3_A_pow8 (Multiplicative.ofAdd (1 : ZMod 8)))
    decide
  · apply multiplicative_zmod_hom_ext
    change (order48_C8_powHom order48_K3_A order48_K3_A_pow8)
        (c2Action_phi3 (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 8))) =
      (MulAut.conj ((order48_C2_powHom order48_K3_B order48_K3_B_pow2)
          (Multiplicative.ofAdd (1 : ZMod 2)))).toMonoidHom
        (order48_C8_powHom order48_K3_A order48_K3_A_pow8 (Multiplicative.ofAdd (1 : ZMod 8)))
    decide

/-- The candidate automorphism `τ : M₁₆ →* M₁₆` sending `a ↦ a·b`, `b ↦ b`. -/
noncomputable def order48_K3_tau : order16_wild_G3 →* order16_wild_G3 :=
  SemidirectProduct.lift (order48_C8_powHom order48_K3_A order48_K3_A_pow8)
    (order48_C2_powHom order48_K3_B order48_K3_B_pow2) order48_K3_tau_compat

theorem order48_K3_tau_bijective : Function.Bijective order48_K3_tau := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

/-- The automorphism `τ : a ↦ a·b, b ↦ b` of `M₁₆`. -/
noncomputable def order48_K3_tau_equiv : order16_wild_G3 ≃* order16_wild_G3 :=
  MulEquiv.ofBijective order48_K3_tau order48_K3_tau_bijective

/-- **`order48_K3_chi_01` and `order48_K3_chi_11` are `Aut(M₁₆)`-orbit-equivalent
via `order48_K3_tau_equiv`** (on generators: `τ(a) = a·b` has `C₈`-sign `−1`
and `C₂`-sign `−1`, matching `chi_11(a) = −1`; `τ(b) = b` keeps the `−1`). -/
theorem order48_K3_chi_01_comp_tau :
    order48_K3_chi_01.comp order48_K3_tau_equiv.toMonoidHom = order48_K3_chi_11 := by
  apply MonoidHom.ext
  decide

/-- **`K₃ = M₁₆` contributes exactly `3` isomorphism classes**: `chi_00`,
`chi_10`, and `chi_01` (merged with `chi_11` via `order48_K3_tau_equiv`). -/
theorem order48_classify_K3_reduced (φ' : order16_wild_G3 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G3 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G3
          (order48_action order48_K3_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G3 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G3
          (order48_action order48_K3_chi_10)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G3 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G3
          (order48_action order48_K3_chi_01)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order48_classify_G3 φ'
  rcases hinl with h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = order48_K3_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = order48_K3_chi_01 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = order48_K3_chi_10 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = order48_K3_chi_11 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ
    obtain ⟨m⟩ := order48_semidirectProduct_of_comp_eq order48_K3_tau_equiv
      order48_K3_chi_01_comp_tau
    exact Or.inr <| Or.inr ⟨e.trans m.symm⟩

/-! ## `K₄ = D₁₆ = C₈ ⋊₇ C₂` (dihedral): `4` raw candidates, one merge -/

noncomputable abbrev order48_K4_chi_00 : order16_wild_G4 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 1 (order48_K4_lift_compat 1 1)
noncomputable abbrev order48_K4_chi_10 : order16_wild_G4 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_signC8 1 (order48_K4_lift_compat _ _)
noncomputable abbrev order48_K4_chi_01 : order16_wild_G4 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift 1 order48_signC2 (order48_K4_lift_compat _ _)
noncomputable abbrev order48_K4_chi_11 : order16_wild_G4 →* (ZMod 3)ˣ :=
  SemidirectProduct.lift order48_signC8 order48_signC2 (order48_K4_lift_compat _ _)

/-! ### The merge `chi_10 ~ chi_11`: the automorphism `σ : a ↦ a, b ↦ a·b` of `D₁₆`

`σ` respects the dihedral relation: `(a·b)² = 1` and
`(a·b)·a·(a·b)⁻¹ = a⁷ = a⁻¹`; verified by `decide` inside
`order48_K4_sigma_compat`. -/

/-- `A = a`: the `C₈`-generator itself. -/
noncomputable def order48_K4_A : order16_wild_G4 :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))

theorem order48_K4_A_pow8 : order48_K4_A ^ 8 = 1 := by decide

/-- The element `B = a·b ∈ D₁₆`: another reflection (order `2`, like all outer
elements of the dihedral group). -/
noncomputable def order48_K4_B : order16_wild_G4 :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8)) *
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem order48_K4_B_pow2 : order48_K4_B ^ 2 = 1 := by decide

/-- The compatibility condition for
`SemidirectProduct.lift (C8_powHom A) (C2_powHom B)`: `B` conjugates `A` by
inversion, matching the dihedral relation. -/
theorem order48_K4_sigma_compat :
    ∀ b, (order48_C8_powHom order48_K4_A order48_K4_A_pow8).comp
        (c2Action_phi4 b).toMonoidHom =
      (MulAut.conj ((order48_C2_powHom order48_K4_B order48_K4_B_pow2) b)).toMonoidHom.comp
        (order48_C8_powHom order48_K4_A order48_K4_A_pow8) := by
  intro b
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · apply multiplicative_zmod_hom_ext
    change (order48_C8_powHom order48_K4_A order48_K4_A_pow8)
        (c2Action_phi4 (1 : Multiplicative (ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 8))) =
      (MulAut.conj ((order48_C2_powHom order48_K4_B order48_K4_B_pow2)
          (1 : Multiplicative (ZMod 2)))).toMonoidHom
        (order48_C8_powHom order48_K4_A order48_K4_A_pow8 (Multiplicative.ofAdd (1 : ZMod 8)))
    decide
  · apply multiplicative_zmod_hom_ext
    change (order48_C8_powHom order48_K4_A order48_K4_A_pow8)
        (c2Action_phi4 (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 8))) =
      (MulAut.conj ((order48_C2_powHom order48_K4_B order48_K4_B_pow2)
          (Multiplicative.ofAdd (1 : ZMod 2)))).toMonoidHom
        (order48_C8_powHom order48_K4_A order48_K4_A_pow8 (Multiplicative.ofAdd (1 : ZMod 8)))
    decide

/-- The candidate automorphism `σ : D₁₆ →* D₁₆` sending `a ↦ a`, `b ↦ a·b`. -/
noncomputable def order48_K4_sigma : order16_wild_G4 →* order16_wild_G4 :=
  SemidirectProduct.lift (order48_C8_powHom order48_K4_A order48_K4_A_pow8)
    (order48_C2_powHom order48_K4_B order48_K4_B_pow2) order48_K4_sigma_compat

theorem order48_K4_sigma_bijective : Function.Bijective order48_K4_sigma := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

/-- The automorphism `σ : a ↦ a, b ↦ a·b` of `D₁₆`. -/
noncomputable def order48_K4_sigma_equiv : order16_wild_G4 ≃* order16_wild_G4 :=
  MulEquiv.ofBijective order48_K4_sigma order48_K4_sigma_bijective

/-- **`order48_K4_chi_10` and `order48_K4_chi_11` are `Aut(D₁₆)`-orbit-equivalent
via `order48_K4_sigma_equiv`** (the two dihedral index-`2` subgroups of `D₁₆`
are `Aut`-conjugate). -/
theorem order48_K4_chi_10_comp_sigma :
    order48_K4_chi_10.comp order48_K4_sigma_equiv.toMonoidHom = order48_K4_chi_11 := by
  apply MonoidHom.ext
  decide

/-- **`K₄ = D₁₆` contributes exactly `3` isomorphism classes**: `chi_00`,
`chi_01` (kernel `C₈`), and `chi_10` (kernel `D₈`, merged with `chi_11` via
`order48_K4_sigma_equiv`). -/
theorem order48_classify_K4_reduced (φ' : order16_wild_G4 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G4
          (order48_action order48_K4_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G4
          (order48_action order48_K4_chi_01)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G4
          (order48_action order48_K4_chi_10)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order48_classify_G4 φ'
  rcases hinl with h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = order48_K4_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = order48_K4_chi_01 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = order48_K4_chi_10 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = order48_K4_chi_11 := SemidirectProduct.hom_ext
      (h1.trans (order48_lift_comp_inl _ _ _).symm)
      (h2.trans (order48_lift_comp_inr _ _ _).symm)
    subst hχ
    obtain ⟨m⟩ := order48_semidirectProduct_of_comp_eq order48_K4_sigma_equiv
      order48_K4_chi_10_comp_sigma
    exact Or.inr <| Or.inr ⟨e.trans m.symm⟩

/-! ## `K₅ = Q₁₆` (`QuaternionGroup 4`, generalised quaternion)

Presentation: `a⁸ = 1`, `b² = a⁴`, `bab⁻¹ = a⁻¹`, with `a = QuaternionGroup.a 1`
and `b = QuaternionGroup.xa 0`.  Every character `Q₁₆ →* (ZMod 3)ˣ` is
`±1`-valued, hence determined by its values on `a` and `b`; the four
combinations are realised by composing the two `Q₁₆ →* C₂` characters from the
order-`80` development (`order80_chiQ16`, `order80_chiQ16_xa`) with
`order48_signC2`. -/

/-- The character with `χ(a) = −1`, `χ(b) = 1` (kernel `Q₈`). -/
noncomputable abbrev order48_chiQ16 : QuaternionGroup 4 →* (ZMod 3)ˣ :=
  order48_signC2.comp order80_chiQ16

/-- The character with `χ(a) = 1`, `χ(b) = −1` (kernel `C₈`). -/
noncomputable abbrev order48_chiQ16_xa : QuaternionGroup 4 →* (ZMod 3)ˣ :=
  order48_signC2.comp order80_chiQ16_xa

/-- The character with `χ(a) = −1`, `χ(b) = −1` (kernel `C₈ ⋊ C₂`-type). -/
noncomputable abbrev order48_chiQ16_prod : QuaternionGroup 4 →* (ZMod 3)ˣ :=
  order48_chiQ16 * order48_chiQ16_xa

@[simp] theorem order48_chiQ16_a1 :
    order48_chiQ16 (QuaternionGroup.a (1 : ZMod 8)) = -1 := by decide

@[simp] theorem order48_chiQ16_x0 :
    order48_chiQ16 (QuaternionGroup.xa (0 : ZMod 8)) = 1 := by decide

@[simp] theorem order48_chiQ16_xa_a1 :
    order48_chiQ16_xa (QuaternionGroup.a (1 : ZMod 8)) = 1 := by decide

@[simp] theorem order48_chiQ16_xa_x0 :
    order48_chiQ16_xa (QuaternionGroup.xa (0 : ZMod 8)) = -1 := by decide

@[simp] theorem order48_chiQ16_prod_a1 :
    order48_chiQ16_prod (QuaternionGroup.a (1 : ZMod 8)) = -1 := by decide

@[simp] theorem order48_chiQ16_prod_x0 :
    order48_chiQ16_prod (QuaternionGroup.xa (0 : ZMod 8)) = -1 := by decide

/-- **Exhaustiveness of characters on `Q₁₆`**: a character `Q₁₆ → (ZMod 3)ˣ` is
one of the four displayed characters. -/
theorem order48_q16_zmod3_character_cases (χ : QuaternionGroup 4 →* (ZMod 3)ˣ) :
    χ = 1 ∨ χ = order48_chiQ16 ∨ χ = order48_chiQ16_xa ∨ χ = order48_chiQ16_prod := by
  let a1 : QuaternionGroup 4 := QuaternionGroup.a (1 : ZMod 8)
  let x0 : QuaternionGroup 4 := QuaternionGroup.xa (0 : ZMod 8)
  rcases zmod3_unit_eq_one_or_neg (χ a1) with ha | ha <;>
    rcases zmod3_unit_eq_one_or_neg (χ x0) with hx | hx
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

/-- **Exhaustiveness for `K = Q₁₆` (`G₅`, action classification)**, in the same
shape as `order48_classify_G2`. -/
theorem order48_classify_G5 (φ' : QuaternionGroup 4 →* MulAut (Multiplicative (ZMod 3))) :
    ∃ χ : QuaternionGroup 4 →* (ZMod 3)ˣ,
      (χ = 1 ∨ χ = order48_chiQ16 ∨ χ = order48_chiQ16_xa ∨ χ = order48_chiQ16_prod) ∧
      Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) (QuaternionGroup 4) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) (QuaternionGroup 4) (order48_action χ)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  exact ⟨ψ, order48_q16_zmod3_character_cases ψ, ⟨semidirectProductCongr_eq hψ⟩⟩

/-! ### The merge: shifting the outer generator `b` by `a`

`σ : a ↦ a, xa i ↦ xa (i+1)` (i.e. `b ↦ a·b`) is an automorphism of `Q₁₆`:
`(a·b)² = a⁴` and `(a·b)·a·(a·b)⁻¹ = a⁻¹`, matching the presentation.  It
merges the `χ(a) = −1, χ(b) = −1` character into the `χ(a) = −1, χ(b) = 1`
one. -/

/-- The automorphism `σ : a ↦ a, b ↦ a·b` of `Q₁₆`. -/
noncomputable def order48_K5_sigma : QuaternionGroup 4 ≃* QuaternionGroup 4 where
  toFun k := match k with
    | QuaternionGroup.a i => QuaternionGroup.a i
    | QuaternionGroup.xa i => QuaternionGroup.xa (i + 1)
  invFun k := match k with
    | QuaternionGroup.a i => QuaternionGroup.a i
    | QuaternionGroup.xa i => QuaternionGroup.xa (i - 1)
  left_inv := by rintro (i | i) <;> simp
  right_inv := by rintro (i | i) <;> simp
  map_mul' := by rintro (i | i) (j | j) <;> revert i j <;> decide

/-- **`order48_chiQ16` and `order48_chiQ16_prod` are `Aut(Q₁₆)`-orbit-equivalent
via `order48_K5_sigma`**: `σ(a) = a` keeps the `−1`, and
`σ(b) = a·b` flips the `b`-value from `1` to `−1`. -/
theorem order48_chiQ16_comp_sigma :
    order48_chiQ16.comp order48_K5_sigma.toMonoidHom = order48_chiQ16_prod := by
  apply MonoidHom.ext
  decide

/-- **`K₅ = Q₁₆` contributes exactly `3` isomorphism classes**: the trivial
character, `order48_chiQ16_xa` (`χ(a) = 1`, `χ(b) = −1`, kernel `C₈`), and
`order48_chiQ16` (`χ(a) = −1`, `χ(b) = 1`, kernel `Q₈`; the `(−1,−1)` character
merges into it via `order48_K5_sigma`). -/
theorem order48_classify_K5_reduced
    (φ' : QuaternionGroup 4 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) (QuaternionGroup 4) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) (QuaternionGroup 4)
          (order48_action (1 : QuaternionGroup 4 →* (ZMod 3)ˣ))) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) (QuaternionGroup 4) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) (QuaternionGroup 4)
          (order48_action order48_chiQ16_xa)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) (QuaternionGroup 4) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) (QuaternionGroup 4)
          (order48_action order48_chiQ16)) := by
  obtain ⟨χ, hcases, ⟨e⟩⟩ := order48_classify_G5 φ'
  rcases hcases with h | h | h | h
  · subst h; exact Or.inl ⟨e⟩
  · subst h; exact Or.inr <| Or.inr ⟨e⟩
  · subst h; exact Or.inr <| Or.inl ⟨e⟩
  · subst h
    obtain ⟨m⟩ := order48_semidirectProduct_of_comp_eq order48_K5_sigma
      order48_chiQ16_comp_sigma
    exact Or.inr <| Or.inr ⟨e.trans m.symm⟩

end Smallgroups.UsefulTheorems
