/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.UniqueSylowThree

/-!
# `C₃ ⋊[χ] K` for the five abelian kernels `K` of order `16`: the reduced classifications

`UniqueSylowThree.lean` reduces the `n₃ = 1` branch of the order-`48` classification to
characters `χ : K →* (ZMod 3)ˣ` (necessarily `±1`-valued) modulo precomposition with
`Aut K` (`order48_semidirectProduct_of_comp_eq`).  This file carries out that orbit
computation for the five **abelian** groups of order `16`, in the same style as the
order-`80` files `UniqueSylowFive_K1to7.lean` / `UniqueSylowFive_K0_K8to13.lean`:

* `K₆ = C₁₆`: `2` classes — trivial, and the sign character (`order48_K6_chi_1`).
* `K₁ = C₈ × C₂`: `3` classes — trivial, `χ(a) = -1, χ(b) = 1` (`order48_K1_chi_1`),
  `χ(a) = 1, χ(b) = -1` (`order48_K1_chi_2`); the fourth character merges into
  `order48_K1_chi_2` via the shear `a ↦ a·b` (`order48_K1_shear`).
* `K₁₃ = C₄ × C₄` (concrete model): `2` classes — trivial, sign on the first factor
  (`order48_K13_chi_1`); the other two nonzero characters merge via the swap and the
  shear `b ↦ a·b`.
* `K₇ = C₄ × C₂ × C₂`: `3` classes — trivial, `χ(a) = -1` alone (`order48_K7_chi_1`,
  kernel `C₂³`), and `χ(b) = -1` (`order48_K7_chi_2`, kernel `C₄ × C₂`); the five
  remaining nonzero characters merge via the swap `b ↔ c`, the shears `b ↦ b·c`,
  `a ↦ a·b` and `a ↦ a·c`.
* `K₀ = (C₂)⁴`: `2` classes — trivial, and the single `Aut(K₀) = GL(4,2)`-orbit of all
  `15` nonzero characters, represented by the sign on the first coordinate
  (`order48_K0_chi_1`).

Each kernel ends in a capstone `order48_classify_K<n>_reduced`.
-/

namespace Smallgroups.UsefulTheorems

/-! ### Sign characters on `C₄` and `C₁₆`

The common `C₄` toolkit is defined in `UniqueSylowThree.lean`; only the
`C₁₆` specialization is defined here. -/

/-- The sign character `C₁₆ →* (ZMod 3)ˣ`, sending the generator to `-1`. -/
noncomputable abbrev order48_signC16 : Multiplicative (ZMod 16) →* (ZMod 3)ˣ :=
  powHom (p := 3) (q := 16) (-1) (by decide)

@[simp]
theorem order48_signC16_gen : order48_signC16 (Multiplicative.ofAdd (1 : ZMod 16)) = -1 := by
  decide

/-- Characters `C₁₆ → (ZMod 3)ˣ` are trivial or `order48_signC16`. -/
theorem c16_zmod3_character_cases (χ : Multiplicative (ZMod 16) →* (ZMod 3)ˣ) :
    χ = 1 ∨ χ = order48_signC16 := by
  rcases zmod3_unit_eq_one_or_neg (χ (Multiplicative.ofAdd (1 : ZMod 16))) with h | h
  · exact Or.inl (multiplicative_zmod_hom_ext (by simp [h]))
  · exact Or.inr (multiplicative_zmod_hom_ext (by rw [h, order48_signC16_gen]))

/-! ## `K₆ = C₁₆`: `2` classes

`Hom(C₁₆, (ZMod 3)ˣ) = {1, sign}` already has two elements, and no merge is needed. -/

/-- The trivial character on `C₁₆`. -/
noncomputable abbrev order48_K6_chi_0 : Multiplicative (ZMod 16) →* (ZMod 3)ˣ := 1

/-- The sign character on `C₁₆` (kernel the `C₈` of even powers). -/
noncomputable abbrev order48_K6_chi_1 : Multiplicative (ZMod 16) →* (ZMod 3)ˣ :=
  order48_signC16

@[simp]
theorem order48_K6_chi_1_gen :
    order48_K6_chi_1 (Multiplicative.ofAdd (1 : ZMod 16)) = -1 := by
  decide

/-- **`K₆ = C₁₆` contributes exactly `2` isomorphism classes.** -/
theorem order48_classify_K6_reduced
    (φ' : Multiplicative (ZMod 16) →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) (Multiplicative (ZMod 16)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) (Multiplicative (ZMod 16))
          (order48_action order48_K6_chi_0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) (Multiplicative (ZMod 16)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) (Multiplicative (ZMod 16))
          (order48_action order48_K6_chi_1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  have e := semidirectProductCongr_eq hψ
  rcases c16_zmod3_character_cases ψ with h | h <;> rw [h] at e
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩

/-! ## `K₁ = C₈ × C₂`: `3` classes

With generators `a` (order `8`) and `b` (order `2`), the four characters are the
independent sign choices on `a` and `b`.  The character `χ(a) = χ(b) = -1`
(`order48_K1_chi_3`) merges into `χ(a) = 1, χ(b) = -1` (`order48_K1_chi_2`) via the
shear `a ↦ a·b, b ↦ b` (`order48_K1_shear`). -/

/-- The trivial character on `K₁`. -/
noncomputable abbrev order48_K1_chi_0 : order16_wild_G1 →* (ZMod 3)ˣ :=
  (1 : C8g →* (ZMod 3)ˣ).coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)

/-- `χ(a) = -1, χ(b) = 1` (kernel `C₄ × C₂`). -/
noncomputable abbrev order48_K1_chi_1 : order16_wild_G1 →* (ZMod 3)ˣ :=
  order48_signC8.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)

/-- `χ(a) = 1, χ(b) = -1` (kernel `C₈`). -/
noncomputable abbrev order48_K1_chi_2 : order16_wild_G1 →* (ZMod 3)ˣ :=
  (1 : C8g →* (ZMod 3)ˣ).coprod order48_signC2

/-- `χ(a) = -1, χ(b) = -1` — merges into `order48_K1_chi_2`. -/
noncomputable abbrev order48_K1_chi_3 : order16_wild_G1 →* (ZMod 3)ˣ :=
  order48_signC8.coprod order48_signC2

@[simp]
theorem order48_K1_chi_1_a :
    order48_K1_chi_1 (Multiplicative.ofAdd (1 : ZMod 8), 1) = -1 := by decide

@[simp]
theorem order48_K1_chi_2_b :
    order48_K1_chi_2 (1, Multiplicative.ofAdd (1 : ZMod 2)) = -1 := by decide

/-- The automorphism of `K₁ = C₈ × C₂` sending `a ↦ a·b`, `b ↦ b`: shears the
`C₂`-part by the image, mod `2`, of the `C₈`-exponent.  Self-inverse since the shift
term has order dividing `2`. -/
noncomputable def order48_K1_shear : order16_wild_G1 ≃* order16_wild_G1 where
  toFun p := (p.1, p.2 * Multiplicative.ofAdd
    ((ZMod.castHom (by norm_num : (2 : ℕ) ∣ 8) (ZMod 2)) (Multiplicative.toAdd p.1)))
  invFun p := (p.1, p.2 * Multiplicative.ofAdd
    ((ZMod.castHom (by norm_num : (2 : ℕ) ∣ 8) (ZMod 2)) (Multiplicative.toAdd p.1)))
  left_inv := by
    rintro ⟨x, y⟩
    ext <;> revert x y <;> decide
  right_inv := by
    rintro ⟨x, y⟩
    ext <;> revert x y <;> decide
  map_mul' := by
    rintro ⟨x1, y1⟩ ⟨x2, y2⟩
    ext <;> revert x1 y1 x2 y2 <;> decide

/-- `χ₂` and `χ₃` are in the same `Aut(K₁)`-orbit, via `order48_K1_shear`. -/
theorem order48_K1_chi_2_comp_shear :
    order48_K1_chi_2.comp order48_K1_shear.toMonoidHom = order48_K1_chi_3 := by
  apply MonoidHom.ext; decide

/-- **`K₁ = C₈ × C₂` contributes exactly `3` isomorphism classes.** -/
theorem order48_classify_K1_reduced (φ' : order16_wild_G1 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G1 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G1
          (order48_action order48_K1_chi_0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G1 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G1
          (order48_action order48_K1_chi_1)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G1 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G1
          (order48_action order48_K1_chi_2)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  have e := semidirectProductCongr_eq hψ
  rw [show ψ = (ψ.comp (MonoidHom.inl _ _)).coprod (ψ.comp (MonoidHom.inr _ _)) from
    (MonoidHom.coprod_unique ψ).symm] at e
  rcases c8_zmod3_character_cases (ψ.comp (MonoidHom.inl _ _)) with h1 | h1 <;>
    rcases c2_zmod3_character_cases (ψ.comp (MonoidHom.inr _ _)) with h2 | h2 <;>
    rw [h1, h2] at e
  · exact Or.inl ⟨e⟩
  · exact Or.inr (Or.inr ⟨e⟩)
  · exact Or.inr (Or.inl ⟨e⟩)
  · exact Or.inr (Or.inr ⟨e.trans (order48_semidirectProduct_of_comp_eq order48_K1_shear
      order48_K1_chi_2_comp_shear).some.symm⟩)

/-! ## `K₁₃ = C₄ × C₄`: `2` classes (concrete model)

`order16_wild_G13 = order16_A3 ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)` via
`order16_A3_iso_concrete`; as in the order-`80` classification we state everything on the
concrete model.  The three nonzero characters are the sign on the first factor
(`order48_K13_chi_1`), the sign on the second (`order48_K13_chi_01`), and the sign on
both (`order48_K13_chi_11`); the latter two merge into the first via the swap and the
shear `b ↦ a·b`. -/

/-- The trivial character on `C₄ × C₄`. -/
noncomputable abbrev order48_K13_chi_0 :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 3)ˣ :=
  (1 : Multiplicative (ZMod 4) →* (ZMod 3)ˣ).coprod (1 : Multiplicative (ZMod 4) →* (ZMod 3)ˣ)

/-- The sign on the first factor (kernel `C₂ × C₄`). -/
noncomputable abbrev order48_K13_chi_1 :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 3)ˣ :=
  order48_signC4.coprod (1 : Multiplicative (ZMod 4) →* (ZMod 3)ˣ)

/-- The sign on the second factor — merges into `order48_K13_chi_1` via the swap. -/
noncomputable abbrev order48_K13_chi_01 :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 3)ˣ :=
  (1 : Multiplicative (ZMod 4) →* (ZMod 3)ˣ).coprod order48_signC4

/-- The sign on both factors — merges into `order48_K13_chi_1` via the shear. -/
noncomputable abbrev order48_K13_chi_11 :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 3)ˣ :=
  order48_signC4.coprod order48_signC4

@[simp]
theorem order48_K13_chi_1_a :
    order48_K13_chi_1 (Multiplicative.ofAdd (1 : ZMod 4), 1) = -1 := by decide

/-- The swap automorphism of `C₄ × C₄`. -/
noncomputable def order48_K13_swap :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4) where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv := by rintro ⟨a, b⟩; rfl
  right_inv := by rintro ⟨a, b⟩; rfl
  map_mul' := by rintro ⟨a, b⟩ ⟨a', b'⟩; rfl

/-- The shear automorphism of `C₄ × C₄` sending `b ↦ a·b` (and fixing `a`). -/
noncomputable def order48_K13_shear :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4) where
  toFun p := (p.1 * p.2, p.2)
  invFun p := (p.1 * p.2⁻¹, p.2)
  left_inv := by rintro ⟨a, b⟩; ext <;> revert a b <;> decide
  right_inv := by rintro ⟨a, b⟩; ext <;> revert a b <;> decide
  map_mul' := by rintro ⟨a, b⟩ ⟨a', b'⟩; ext <;> revert a b a' b' <;> decide

theorem order48_K13_chi_1_comp_swap :
    order48_K13_chi_1.comp order48_K13_swap.toMonoidHom = order48_K13_chi_01 := by
  apply MonoidHom.ext; decide

theorem order48_K13_chi_1_comp_shear :
    order48_K13_chi_1.comp order48_K13_shear.toMonoidHom = order48_K13_chi_11 := by
  apply MonoidHom.ext; decide

/-- **`K₁₃ = C₄ × C₄` contributes exactly `2` isomorphism classes.** -/
theorem order48_classify_K13_reduced
    (φ' : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →*
      MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3))
          (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
          (order48_action order48_K13_chi_0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3))
          (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
          (order48_action order48_K13_chi_1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  have e := semidirectProductCongr_eq hψ
  rw [show ψ = (ψ.comp (MonoidHom.inl _ _)).coprod (ψ.comp (MonoidHom.inr _ _)) from
    (MonoidHom.coprod_unique ψ).symm] at e
  rcases c4_zmod3_character_cases (ψ.comp (MonoidHom.inl _ _)) with h1 | h1 <;>
    rcases c4_zmod3_character_cases (ψ.comp (MonoidHom.inr _ _)) with h2 | h2 <;>
    rw [h1, h2] at e
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e.trans (order48_semidirectProduct_of_comp_eq order48_K13_swap
      order48_K13_chi_1_comp_swap).some.symm⟩
  · exact Or.inr ⟨e⟩
  · exact Or.inr ⟨e.trans (order48_semidirectProduct_of_comp_eq order48_K13_shear
      order48_K13_chi_1_comp_shear).some.symm⟩

/-! ## `K₇ = C₄ × C₂ × C₂`: `3` classes

`order16_wild_G7 = K8g × C₂ = (C₄ × C₂) × C₂` with generators `a` (order `4`), `b`
(inner `C₂`), `c` (outer `C₂`).  A character is a triple of signs `(χ(a), χ(b), χ(c))`.
The kernel contains an element of order `4` iff `χ(a) = 1` or one of `χ(b), χ(c)` is
`-1`; hence the only character with elementary abelian kernel `C₂³` is
`(−1, 1, 1)` (`order48_K7_chi_1`), and every other nonzero character has kernel of type
`C₄ × C₂` and merges into `(1, −1, 1)` (`order48_K7_chi_2`) via the automorphisms
`b ↔ c` (`order48_K7_swapbc`), `b ↦ b·c` (`order48_K7_shear_bc`), `a ↦ a·b`
(`order48_K7_shear_ab`) and `a ↦ a·c` (`order48_K7_shear_ac`). -/

/-- The trivial character on `K₇`. -/
noncomputable abbrev order48_K7_chi_0 : order16_wild_G7 →* (ZMod 3)ˣ :=
  ((1 : Multiplicative (ZMod 4) →* (ZMod 3)ˣ).coprod
    (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)).coprod
    (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)

/-- `(χ(a), χ(b), χ(c)) = (−1, 1, 1)` (kernel `C₂³`). -/
noncomputable abbrev order48_K7_chi_1 : order16_wild_G7 →* (ZMod 3)ˣ :=
  (order48_signC4.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)).coprod
    (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)

/-- `(χ(a), χ(b), χ(c)) = (1, −1, 1)` (kernel `C₄ × C₂`). -/
noncomputable abbrev order48_K7_chi_2 : order16_wild_G7 →* (ZMod 3)ˣ :=
  ((1 : Multiplicative (ZMod 4) →* (ZMod 3)ˣ).coprod order48_signC2).coprod
    (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)

/-- `(1, 1, −1)` — merges into `order48_K7_chi_2` via `b ↔ c`. -/
noncomputable abbrev order48_K7_chi_001 : order16_wild_G7 →* (ZMod 3)ˣ :=
  ((1 : Multiplicative (ZMod 4) →* (ZMod 3)ˣ).coprod
    (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)).coprod order48_signC2

/-- `(1, −1, −1)` — merges into `order48_K7_chi_2` via `b ↦ b·c`. -/
noncomputable abbrev order48_K7_chi_011 : order16_wild_G7 →* (ZMod 3)ˣ :=
  ((1 : Multiplicative (ZMod 4) →* (ZMod 3)ˣ).coprod order48_signC2).coprod order48_signC2

/-- `(−1, 1, −1)` — merges into `order48_K7_chi_001` via `a ↦ a·c`. -/
noncomputable abbrev order48_K7_chi_101 : order16_wild_G7 →* (ZMod 3)ˣ :=
  (order48_signC4.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)).coprod order48_signC2

/-- `(−1, −1, 1)` — merges into `order48_K7_chi_2` via `a ↦ a·b`. -/
noncomputable abbrev order48_K7_chi_110 : order16_wild_G7 →* (ZMod 3)ˣ :=
  (order48_signC4.coprod order48_signC2).coprod
    (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)

/-- `(−1, −1, −1)` — merges into `order48_K7_chi_011` via `a ↦ a·b`. -/
noncomputable abbrev order48_K7_chi_111 : order16_wild_G7 →* (ZMod 3)ˣ :=
  (order48_signC4.coprod order48_signC2).coprod order48_signC2

@[simp]
theorem order48_K7_chi_1_a :
    order48_K7_chi_1 ((Multiplicative.ofAdd (1 : ZMod 4), 1), 1) = -1 := by decide

@[simp]
theorem order48_K7_chi_2_b :
    order48_K7_chi_2 ((1, Multiplicative.ofAdd (1 : ZMod 2)), 1) = -1 := by decide

/-- Swapping the two `C₂`-factors `b` (inside `K₈g`) and `c` (the outer `C₂`). -/
noncomputable def order48_K7_swapbc : order16_wild_G7 ≃* order16_wild_G7 where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv := by rintro ⟨⟨_, _⟩, _⟩; rfl
  right_inv := by rintro ⟨⟨_, _⟩, _⟩; rfl
  map_mul' := by rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩; rfl

/-- Shears `b` by `c` (fixing `a, c`). -/
noncomputable def order48_K7_shear_bc : order16_wild_G7 ≃* order16_wild_G7 where
  toFun p := ((p.1.1, p.1.2 * p.2), p.2)
  invFun p := ((p.1.1, p.1.2 * p.2), p.2)
  left_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  right_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  map_mul' := by
    rintro ⟨⟨x1, y1⟩, z1⟩ ⟨⟨x2, y2⟩, z2⟩
    ext <;> revert x1 y1 z1 x2 y2 z2 <;> decide

/-- The mod-`2` projection `C₄ → C₂`. -/
noncomputable def order48_K7_pi : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (ZMod.castHom (by norm_num : (2:ℕ) ∣ 4) (ZMod 2)
    (Multiplicative.toAdd x))) (fun _ _ => by simp [ofAdd_add])

/-- Shears `b` by `π(a)` (fixing `a, c`): the automorphism `a ↦ a·b, b ↦ b, c ↦ c`. -/
noncomputable def order48_K7_shear_ab : order16_wild_G7 ≃* order16_wild_G7 where
  toFun p := ((p.1.1, p.1.2 * order48_K7_pi p.1.1), p.2)
  invFun p := ((p.1.1, p.1.2 * order48_K7_pi p.1.1), p.2)
  left_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  right_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  map_mul' := by
    rintro ⟨⟨x1, y1⟩, z1⟩ ⟨⟨x2, y2⟩, z2⟩
    ext <;> revert x1 y1 z1 x2 y2 z2 <;> decide

/-- Shears `c` by `π(a)` (fixing `a, b`): the automorphism `a ↦ a·c, b ↦ b, c ↦ c`. -/
noncomputable def order48_K7_shear_ac : order16_wild_G7 ≃* order16_wild_G7 where
  toFun p := ((p.1.1, p.1.2), p.2 * order48_K7_pi p.1.1)
  invFun p := ((p.1.1, p.1.2), p.2 * order48_K7_pi p.1.1)
  left_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  right_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  map_mul' := by
    rintro ⟨⟨x1, y1⟩, z1⟩ ⟨⟨x2, y2⟩, z2⟩
    ext <;> revert x1 y1 z1 x2 y2 z2 <;> decide

theorem order48_K7_chi_2_comp_swapbc :
    order48_K7_chi_2.comp order48_K7_swapbc.toMonoidHom = order48_K7_chi_001 := by
  apply MonoidHom.ext; decide

theorem order48_K7_chi_2_comp_shear_bc :
    order48_K7_chi_2.comp order48_K7_shear_bc.toMonoidHom = order48_K7_chi_011 := by
  apply MonoidHom.ext; decide

theorem order48_K7_chi_110_comp_shear_ab :
    order48_K7_chi_110.comp order48_K7_shear_ab.toMonoidHom = order48_K7_chi_2 := by
  apply MonoidHom.ext; decide

theorem order48_K7_chi_101_comp_shear_ac :
    order48_K7_chi_101.comp order48_K7_shear_ac.toMonoidHom = order48_K7_chi_001 := by
  apply MonoidHom.ext; decide

theorem order48_K7_chi_111_comp_shear_ab :
    order48_K7_chi_111.comp order48_K7_shear_ab.toMonoidHom = order48_K7_chi_011 := by
  apply MonoidHom.ext; decide

/-- **`K₇ = C₄ × C₂ × C₂` contributes exactly `3` isomorphism classes.** -/
theorem order48_classify_K7_reduced (φ' : order16_wild_G7 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G7 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G7
          (order48_action order48_K7_chi_0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G7 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G7
          (order48_action order48_K7_chi_1)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G7 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_G7
          (order48_action order48_K7_chi_2)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  have e := semidirectProductCongr_eq hψ
  have hχ2 : ψ.comp (MonoidHom.inl _ _) =
      ((ψ.comp (MonoidHom.inl _ _)).comp (MonoidHom.inl _ _)).coprod
        ((ψ.comp (MonoidHom.inl _ _)).comp (MonoidHom.inr _ _)) :=
    (MonoidHom.coprod_unique _).symm
  have hχ : ψ = (ψ.comp (MonoidHom.inl _ _)).coprod (ψ.comp (MonoidHom.inr _ _)) :=
    (MonoidHom.coprod_unique ψ).symm
  rw [hχ2] at hχ
  rw [hχ] at e
  rcases c4_zmod3_character_cases ((ψ.comp (MonoidHom.inl _ _)).comp (MonoidHom.inl _ _)) with
    h1 | h1 <;>
    rcases c2_zmod3_character_cases ((ψ.comp (MonoidHom.inl _ _)).comp (MonoidHom.inr _ _)) with
      h2 | h2 <;>
    rcases c2_zmod3_character_cases (ψ.comp (MonoidHom.inr _ _)) with h3 | h3 <;>
    rw [h1, h2, h3] at e
  · exact Or.inl ⟨e⟩
  · exact Or.inr (Or.inr ⟨e.trans (order48_semidirectProduct_of_comp_eq order48_K7_swapbc
      order48_K7_chi_2_comp_swapbc).some.symm⟩)
  · exact Or.inr (Or.inr ⟨e⟩)
  · exact Or.inr (Or.inr ⟨e.trans (order48_semidirectProduct_of_comp_eq order48_K7_shear_bc
      order48_K7_chi_2_comp_shear_bc).some.symm⟩)
  · exact Or.inr (Or.inl ⟨e⟩)
  · exact Or.inr (Or.inr ⟨e.trans ((order48_semidirectProduct_of_comp_eq order48_K7_shear_ac
      order48_K7_chi_101_comp_shear_ac).some.trans (order48_semidirectProduct_of_comp_eq
        order48_K7_swapbc order48_K7_chi_2_comp_swapbc).some.symm)⟩)
  · exact Or.inr (Or.inr ⟨e.trans (order48_semidirectProduct_of_comp_eq order48_K7_shear_ab
      order48_K7_chi_110_comp_shear_ab).some⟩)
  · exact Or.inr (Or.inr ⟨e.trans ((order48_semidirectProduct_of_comp_eq order48_K7_shear_ab
      order48_K7_chi_111_comp_shear_ab).some.trans (order48_semidirectProduct_of_comp_eq
        order48_K7_shear_bc order48_K7_chi_2_comp_shear_bc).some.symm)⟩)

/-! ## `K₀ = (C₂)⁴`: `2` classes

A character of `(C₂)⁴` is a `4`-tuple of signs, i.e. a vector of
`Hom((C₂)⁴, (ZMod 3)ˣ) ≅ (C₂)⁴`.  `Aut(K₀) = GL(4,2)` acts transitively on the `15`
nonzero vectors; we exhibit the merges explicitly with coordinate swaps
(`order48_K0_swap<i><j>`) and shears `e₁ ↦ e₁·eⱼ` (`order48_K0_shear<j>1`), with hub the
sign on the first coordinate (`order48_K0_chi_1`). -/

/-- The trivial character on `(C₂)⁴`. -/
noncomputable abbrev order48_K0_chi_0 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)))

/-- The sign on the first coordinate (representative of the nonzero orbit). -/
noncomputable abbrev order48_K0_chi_1 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  order48_signC2.coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)))

noncomputable abbrev order48_K0_chi_0100 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
    (order48_signC2.coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)))

noncomputable abbrev order48_K0_chi_0010 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      (order48_signC2.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)))

noncomputable abbrev order48_K0_chi_0001 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod order48_signC2))

noncomputable abbrev order48_K0_chi_1100 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  order48_signC2.coprod
    (order48_signC2.coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)))

noncomputable abbrev order48_K0_chi_1010 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  order48_signC2.coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      (order48_signC2.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)))

noncomputable abbrev order48_K0_chi_1001 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  order48_signC2.coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod order48_signC2))

noncomputable abbrev order48_K0_chi_0110 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
    (order48_signC2.coprod
      (order48_signC2.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)))

noncomputable abbrev order48_K0_chi_0101 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
    (order48_signC2.coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod order48_signC2))

noncomputable abbrev order48_K0_chi_0011 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      (order48_signC2.coprod order48_signC2))

noncomputable abbrev order48_K0_chi_1110 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  order48_signC2.coprod
    (order48_signC2.coprod
      (order48_signC2.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ)))

noncomputable abbrev order48_K0_chi_1101 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  order48_signC2.coprod
    (order48_signC2.coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod order48_signC2))

noncomputable abbrev order48_K0_chi_1011 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  order48_signC2.coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
      (order48_signC2.coprod order48_signC2))

noncomputable abbrev order48_K0_chi_0111 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 3)ˣ).coprod
    (order48_signC2.coprod
      (order48_signC2.coprod order48_signC2))

noncomputable abbrev order48_K0_chi_1111 : order16_wild_C2pow4 →* (ZMod 3)ˣ :=
  order48_signC2.coprod
    (order48_signC2.coprod
      (order48_signC2.coprod order48_signC2))

@[simp]
theorem order48_K0_chi_1_e1 :
    order48_K0_chi_1 (Multiplicative.ofAdd (1 : ZMod 2), (1, (1, 1))) = -1 := by decide

/-! ### Automorphisms of `(C₂)⁴`: coordinate swaps and shears -/

/-- Swap coordinates `1` and `2`. -/
noncomputable def order48_K0_swap12 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.2.1, (p.1, (p.2.2.1, p.2.2.2)))
  invFun p := (p.2.1, (p.1, (p.2.2.1, p.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl
  map_mul' := by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; rfl

/-- Swap coordinates `1` and `3`. -/
noncomputable def order48_K0_swap13 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.2.2.1, (p.2.1, (p.1, p.2.2.2)))
  invFun p := (p.2.2.1, (p.2.1, (p.1, p.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl
  map_mul' := by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; rfl

/-- Swap coordinates `1` and `4`. -/
noncomputable def order48_K0_swap14 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.2.2.2, (p.2.1, (p.2.2.1, p.1)))
  invFun p := (p.2.2.2, (p.2.1, (p.2.2.1, p.1)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl
  map_mul' := by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; rfl

/-- Swap coordinates `2` and `4`. -/
noncomputable def order48_K0_swap24 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.1, (p.2.2.2, (p.2.2.1, p.2.1)))
  invFun p := (p.1, (p.2.2.2, (p.2.2.1, p.2.1)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl
  map_mul' := by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; rfl

/-- Swap coordinates `3` and `4`. -/
noncomputable def order48_K0_swap34 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.1, (p.2.1, (p.2.2.2, p.2.2.1)))
  invFun p := (p.1, (p.2.1, (p.2.2.2, p.2.2.1)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl
  map_mul' := by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; rfl

/-- Shear `e₁ ↦ e₁·e₂`. -/
noncomputable def order48_K0_shear21 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.1 * p.2.1, (p.2.1, (p.2.2.1, p.2.2.2)))
  invFun p := (p.1 * p.2.1, (p.2.1, (p.2.2.1, p.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  right_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  map_mul' := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; ext <;> revert a b c d a' b' c' d' <;> decide

/-- Shear `e₁ ↦ e₁·e₃`. -/
noncomputable def order48_K0_shear31 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.1 * p.2.2.1, (p.2.1, (p.2.2.1, p.2.2.2)))
  invFun p := (p.1 * p.2.2.1, (p.2.1, (p.2.2.1, p.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  right_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  map_mul' := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; ext <;> revert a b c d a' b' c' d' <;> decide

/-- Shear `e₁ ↦ e₁·e₄`. -/
noncomputable def order48_K0_shear41 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.1 * p.2.2.2, (p.2.1, (p.2.2.1, p.2.2.2)))
  invFun p := (p.1 * p.2.2.2, (p.2.1, (p.2.2.1, p.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  right_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  map_mul' := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; ext <;> revert a b c d a' b' c' d' <;> decide

/-! ### All `15` nonzero characters lie in a single `Aut(K₀)`-orbit -/

theorem order48_K0_chi_1_comp_swap12 :
    order48_K0_chi_1.comp order48_K0_swap12.toMonoidHom = order48_K0_chi_0100 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1_comp_swap13 :
    order48_K0_chi_1.comp order48_K0_swap13.toMonoidHom = order48_K0_chi_0010 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1_comp_swap14 :
    order48_K0_chi_1.comp order48_K0_swap14.toMonoidHom = order48_K0_chi_0001 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1_comp_shear21 :
    order48_K0_chi_1.comp order48_K0_shear21.toMonoidHom = order48_K0_chi_1100 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1_comp_shear31 :
    order48_K0_chi_1.comp order48_K0_shear31.toMonoidHom = order48_K0_chi_1010 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1_comp_shear41 :
    order48_K0_chi_1.comp order48_K0_shear41.toMonoidHom = order48_K0_chi_1001 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1010_comp_swap12 :
    order48_K0_chi_1010.comp order48_K0_swap12.toMonoidHom = order48_K0_chi_0110 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1001_comp_swap12 :
    order48_K0_chi_1001.comp order48_K0_swap12.toMonoidHom = order48_K0_chi_0101 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1001_comp_swap13 :
    order48_K0_chi_1001.comp order48_K0_swap13.toMonoidHom = order48_K0_chi_0011 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1100_comp_shear31 :
    order48_K0_chi_1100.comp order48_K0_shear31.toMonoidHom = order48_K0_chi_1110 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1110_comp_swap34 :
    order48_K0_chi_1110.comp order48_K0_swap34.toMonoidHom = order48_K0_chi_1101 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1110_comp_swap24 :
    order48_K0_chi_1110.comp order48_K0_swap24.toMonoidHom = order48_K0_chi_1011 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1110_comp_swap14 :
    order48_K0_chi_1110.comp order48_K0_swap14.toMonoidHom = order48_K0_chi_0111 := by
  apply MonoidHom.ext; decide
theorem order48_K0_chi_1110_comp_shear41 :
    order48_K0_chi_1110.comp order48_K0_shear41.toMonoidHom = order48_K0_chi_1111 := by
  apply MonoidHom.ext; decide

/-- Every nonzero raw character of `K₀ = (C₂)⁴` is `Aut(K₀)`-equivalent to
`order48_K0_chi_1`. -/
theorem order48_K0_iso_std_of_ne_zero (χ : order16_wild_C2pow4 →* (ZMod 3)ˣ)
    (h : χ = order48_K0_chi_1 ∨ χ = order48_K0_chi_0100 ∨ χ = order48_K0_chi_0010 ∨
      χ = order48_K0_chi_0001 ∨ χ = order48_K0_chi_1100 ∨ χ = order48_K0_chi_1010 ∨
      χ = order48_K0_chi_1001 ∨ χ = order48_K0_chi_0110 ∨ χ = order48_K0_chi_0101 ∨
      χ = order48_K0_chi_0011 ∨ χ = order48_K0_chi_1110 ∨ χ = order48_K0_chi_1101 ∨
      χ = order48_K0_chi_1011 ∨ χ = order48_K0_chi_0111 ∨ χ = order48_K0_chi_1111) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_C2pow4
      (order48_action order48_K0_chi_1) ≃*
      SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_C2pow4
        (order48_action χ)) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact ⟨MulEquiv.refl _⟩
  · exact order48_semidirectProduct_of_comp_eq order48_K0_swap12 order48_K0_chi_1_comp_swap12
  · exact order48_semidirectProduct_of_comp_eq order48_K0_swap13 order48_K0_chi_1_comp_swap13
  · exact order48_semidirectProduct_of_comp_eq order48_K0_swap14 order48_K0_chi_1_comp_swap14
  · exact order48_semidirectProduct_of_comp_eq order48_K0_shear21 order48_K0_chi_1_comp_shear21
  · exact order48_semidirectProduct_of_comp_eq order48_K0_shear31 order48_K0_chi_1_comp_shear31
  · exact order48_semidirectProduct_of_comp_eq order48_K0_shear41 order48_K0_chi_1_comp_shear41
  · exact ⟨(order48_semidirectProduct_of_comp_eq order48_K0_shear31
      order48_K0_chi_1_comp_shear31).some.trans
      (order48_semidirectProduct_of_comp_eq order48_K0_swap12
        order48_K0_chi_1010_comp_swap12).some⟩
  · exact ⟨(order48_semidirectProduct_of_comp_eq order48_K0_shear41
      order48_K0_chi_1_comp_shear41).some.trans
      (order48_semidirectProduct_of_comp_eq order48_K0_swap12
        order48_K0_chi_1001_comp_swap12).some⟩
  · exact ⟨(order48_semidirectProduct_of_comp_eq order48_K0_shear41
      order48_K0_chi_1_comp_shear41).some.trans
      (order48_semidirectProduct_of_comp_eq order48_K0_swap13
        order48_K0_chi_1001_comp_swap13).some⟩
  · exact ⟨(order48_semidirectProduct_of_comp_eq order48_K0_shear21
      order48_K0_chi_1_comp_shear21).some.trans
      (order48_semidirectProduct_of_comp_eq order48_K0_shear31
        order48_K0_chi_1100_comp_shear31).some⟩
  · exact ⟨(order48_semidirectProduct_of_comp_eq order48_K0_shear21
      order48_K0_chi_1_comp_shear21).some.trans
      ((order48_semidirectProduct_of_comp_eq order48_K0_shear31
        order48_K0_chi_1100_comp_shear31).some.trans
        (order48_semidirectProduct_of_comp_eq order48_K0_swap34
          order48_K0_chi_1110_comp_swap34).some)⟩
  · exact ⟨(order48_semidirectProduct_of_comp_eq order48_K0_shear21
      order48_K0_chi_1_comp_shear21).some.trans
      ((order48_semidirectProduct_of_comp_eq order48_K0_shear31
        order48_K0_chi_1100_comp_shear31).some.trans
        (order48_semidirectProduct_of_comp_eq order48_K0_swap24
          order48_K0_chi_1110_comp_swap24).some)⟩
  · exact ⟨(order48_semidirectProduct_of_comp_eq order48_K0_shear21
      order48_K0_chi_1_comp_shear21).some.trans
      ((order48_semidirectProduct_of_comp_eq order48_K0_shear31
        order48_K0_chi_1100_comp_shear31).some.trans
        (order48_semidirectProduct_of_comp_eq order48_K0_swap14
          order48_K0_chi_1110_comp_swap14).some)⟩
  · exact ⟨(order48_semidirectProduct_of_comp_eq order48_K0_shear21
      order48_K0_chi_1_comp_shear21).some.trans
      ((order48_semidirectProduct_of_comp_eq order48_K0_shear31
        order48_K0_chi_1100_comp_shear31).some.trans
        (order48_semidirectProduct_of_comp_eq order48_K0_shear41
          order48_K0_chi_1110_comp_shear41).some)⟩

/-- **`K₀ = (C₂)⁴` contributes exactly `2` isomorphism classes**: the trivial action and
the single class of all `15` nonzero characters, since `Aut(K₀) = GL(4,2)` acts
transitively on the nonzero vectors of `Hom((C₂)⁴, (ZMod 3)ˣ) ≅ (C₂)⁴`. -/
theorem order48_classify_K0_reduced
    (φ' : order16_wild_C2pow4 →* MulAut (Multiplicative (ZMod 3))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_C2pow4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_C2pow4
          (order48_action order48_K0_chi_0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_C2pow4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 3)) order16_wild_C2pow4
          (order48_action order48_K0_chi_1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  have e := semidirectProductCongr_eq hψ
  have hχ4 : ψ.comp (MonoidHom.inr _ _) =
      ((ψ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inl _ _)).coprod
        ((ψ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)) :=
    (MonoidHom.coprod_unique _).symm
  have hχ3 : (ψ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _) =
      (((ψ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)).comp (MonoidHom.inl _ _)).coprod
        (((ψ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)) :=
    (MonoidHom.coprod_unique _).symm
  have hχ : ψ = (ψ.comp (MonoidHom.inl _ _)).coprod (ψ.comp (MonoidHom.inr _ _)) :=
    (MonoidHom.coprod_unique ψ).symm
  rw [hχ3] at hχ4
  rw [hχ4] at hχ
  rw [hχ] at e
  rcases c2_zmod3_character_cases (ψ.comp (MonoidHom.inl _ _)) with h1 | h1 <;>
    rcases c2_zmod3_character_cases ((ψ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inl _ _)) with
      h2 | h2 <;>
    rcases c2_zmod3_character_cases
      (((ψ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)).comp (MonoidHom.inl _ _)) with
      h3 | h3 <;>
    rcases c2_zmod3_character_cases
      (((ψ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)) with
      h4 | h4 <;>
    rw [h1, h2, h3, h4] at e
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr
    (Or.inl rfl))))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr
    (Or.inl rfl)))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr
    (Or.inl rfl))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl rfl)))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl rfl))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))).some.symm⟩
  · exact Or.inr ⟨e⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl rfl)))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl rfl))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl rfl)))))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (order48_K0_iso_std_of_ne_zero _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))))))))).some.symm⟩

end Smallgroups.UsefulTheorems
