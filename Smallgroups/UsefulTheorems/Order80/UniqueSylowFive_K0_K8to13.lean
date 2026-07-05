/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order80.UniqueSylowFive_K1to7

/-!
# Isomorphism classes of `C₅ ⋊ Kᵢ` for `i = 0, 8, 9, 10, 11, 12, 13`

Continues `UniqueSylowFive_K1to7.lean` (which handles `K₁`–`K₇`) for the remaining seven of the
fourteen isomorphism types `K` of order-`16` groups arising as complements in the Sylow-`5`-unique
branch of the order-`80` classification. Reuses all the general tools from that file
(`semidirectProduct_of_comp_eq`, `order80_ne_of_ker_card`, `order80_ne_of_ker_order`, etc.)
without re-deriving them.
-/

namespace Smallgroups.UsefulTheorems

/-! ## `K₀ = (C₂)⁴` (elementary abelian) -/

noncomputable abbrev K0_chi_0000 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)))

noncomputable abbrev K0_chi_1000 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)))

noncomputable abbrev K0_chi_0100 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
    (order40_c2UnitHom.coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)))

noncomputable abbrev K0_chi_0010 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      (order40_c2UnitHom.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)))

noncomputable abbrev K0_chi_0001 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod order40_c2UnitHom))

noncomputable abbrev K0_chi_1100 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.coprod
    (order40_c2UnitHom.coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)))

noncomputable abbrev K0_chi_1010 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      (order40_c2UnitHom.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)))

noncomputable abbrev K0_chi_1001 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod order40_c2UnitHom))

noncomputable abbrev K0_chi_0110 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
    (order40_c2UnitHom.coprod
      (order40_c2UnitHom.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)))

noncomputable abbrev K0_chi_0101 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
    (order40_c2UnitHom.coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod order40_c2UnitHom))

noncomputable abbrev K0_chi_0011 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      (order40_c2UnitHom.coprod order40_c2UnitHom))

noncomputable abbrev K0_chi_1110 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.coprod
    (order40_c2UnitHom.coprod
      (order40_c2UnitHom.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)))

noncomputable abbrev K0_chi_1101 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.coprod
    (order40_c2UnitHom.coprod
      ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod order40_c2UnitHom))

noncomputable abbrev K0_chi_1011 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.coprod
    ((1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
      (order40_c2UnitHom.coprod order40_c2UnitHom))

noncomputable abbrev K0_chi_0111 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ).coprod
    (order40_c2UnitHom.coprod
      (order40_c2UnitHom.coprod order40_c2UnitHom))

noncomputable abbrev K0_chi_1111 : order16_wild_C2pow4 →* (ZMod 5)ˣ :=
  order40_c2UnitHom.coprod
    (order40_c2UnitHom.coprod
      (order40_c2UnitHom.coprod order40_c2UnitHom))

theorem order16_wild_C2pow4_coprime : Nat.Coprime 5 (Fintype.card order16_wild_C2pow4) := by
  decide

theorem K0_chi_0000_ker_card :
    Fintype.card {k : order16_wild_C2pow4 // K0_chi_0000 k = 1} = 16 := by decide
theorem K0_chi_1000_ker_card :
    Fintype.card {k : order16_wild_C2pow4 // K0_chi_1000 k = 1} = 8 := by decide

/-! ### Automorphisms of `(C₂)⁴`: coordinate swaps and shears -/

noncomputable def K0_swap12 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.2.1, (p.1, (p.2.2.1, p.2.2.2)))
  invFun p := (p.2.1, (p.1, (p.2.2.1, p.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl
  map_mul' := by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; rfl

noncomputable def K0_swap13 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.2.2.1, (p.2.1, (p.1, p.2.2.2)))
  invFun p := (p.2.2.1, (p.2.1, (p.1, p.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl
  map_mul' := by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; rfl

noncomputable def K0_swap14 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.2.2.2, (p.2.1, (p.2.2.1, p.1)))
  invFun p := (p.2.2.2, (p.2.1, (p.2.2.1, p.1)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl
  map_mul' := by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; rfl

noncomputable def K0_swap24 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.1, (p.2.2.2, (p.2.2.1, p.2.1)))
  invFun p := (p.1, (p.2.2.2, (p.2.2.1, p.2.1)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl
  map_mul' := by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; rfl

noncomputable def K0_swap34 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.1, (p.2.1, (p.2.2.2, p.2.2.1)))
  invFun p := (p.1, (p.2.1, (p.2.2.2, p.2.2.1)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl
  map_mul' := by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; rfl

noncomputable def K0_shear21 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.1 * p.2.1, (p.2.1, (p.2.2.1, p.2.2.2)))
  invFun p := (p.1 * p.2.1, (p.2.1, (p.2.2.1, p.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  right_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  map_mul' := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; ext <;> revert a b c d a' b' c' d' <;> decide

noncomputable def K0_shear31 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.1 * p.2.2.1, (p.2.1, (p.2.2.1, p.2.2.2)))
  invFun p := (p.1 * p.2.2.1, (p.2.1, (p.2.2.1, p.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  right_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  map_mul' := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; ext <;> revert a b c d a' b' c' d' <;> decide

noncomputable def K0_shear41 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.1 * p.2.2.2, (p.2.1, (p.2.2.1, p.2.2.2)))
  invFun p := (p.1 * p.2.2.2, (p.2.1, (p.2.2.1, p.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  right_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  map_mul' := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; ext <;> revert a b c d a' b' c' d' <;> decide

/-! ### All `15` nonzero characters lie in a single `Aut(K₀)`-orbit -/

theorem K0_chi_1000_comp_swap12 : K0_chi_1000.comp K0_swap12.toMonoidHom = K0_chi_0100 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1000_comp_swap13 : K0_chi_1000.comp K0_swap13.toMonoidHom = K0_chi_0010 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1000_comp_swap14 : K0_chi_1000.comp K0_swap14.toMonoidHom = K0_chi_0001 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1000_comp_shear21 : K0_chi_1000.comp K0_shear21.toMonoidHom = K0_chi_1100 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1000_comp_shear31 : K0_chi_1000.comp K0_shear31.toMonoidHom = K0_chi_1010 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1000_comp_shear41 : K0_chi_1000.comp K0_shear41.toMonoidHom = K0_chi_1001 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1010_comp_swap12 : K0_chi_1010.comp K0_swap12.toMonoidHom = K0_chi_0110 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1001_comp_swap12 : K0_chi_1001.comp K0_swap12.toMonoidHom = K0_chi_0101 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1001_comp_swap13 : K0_chi_1001.comp K0_swap13.toMonoidHom = K0_chi_0011 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1100_comp_shear31 : K0_chi_1100.comp K0_shear31.toMonoidHom = K0_chi_1110 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1110_comp_shear41 : K0_chi_1110.comp K0_shear41.toMonoidHom = K0_chi_1111 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1110_comp_swap34 : K0_chi_1110.comp K0_swap34.toMonoidHom = K0_chi_1101 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1110_comp_swap24 : K0_chi_1110.comp K0_swap24.toMonoidHom = K0_chi_1011 := by
  apply MonoidHom.ext; decide
theorem K0_chi_1110_comp_swap14 : K0_chi_1110.comp K0_swap14.toMonoidHom = K0_chi_0111 := by
  apply MonoidHom.ext; decide

theorem K0_iso_1000_0100 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1000) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_0100)) :=
  semidirectProduct_of_comp_eq K0_swap12 K0_chi_1000_comp_swap12
theorem K0_iso_1000_0010 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1000) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_0010)) :=
  semidirectProduct_of_comp_eq K0_swap13 K0_chi_1000_comp_swap13
theorem K0_iso_1000_0001 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1000) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_0001)) :=
  semidirectProduct_of_comp_eq K0_swap14 K0_chi_1000_comp_swap14
theorem K0_iso_1000_1100 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1000) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_1100)) :=
  semidirectProduct_of_comp_eq K0_shear21 K0_chi_1000_comp_shear21
theorem K0_iso_1000_1010 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1000) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_1010)) :=
  semidirectProduct_of_comp_eq K0_shear31 K0_chi_1000_comp_shear31
theorem K0_iso_1000_1001 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1000) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_1001)) :=
  semidirectProduct_of_comp_eq K0_shear41 K0_chi_1000_comp_shear41
theorem K0_iso_1010_0110 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1010) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_0110)) :=
  semidirectProduct_of_comp_eq K0_swap12 K0_chi_1010_comp_swap12
theorem K0_iso_1001_0101 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1001) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_0101)) :=
  semidirectProduct_of_comp_eq K0_swap12 K0_chi_1001_comp_swap12
theorem K0_iso_1001_0011 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1001) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_0011)) :=
  semidirectProduct_of_comp_eq K0_swap13 K0_chi_1001_comp_swap13
theorem K0_iso_1100_1110 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1100) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_1110)) :=
  semidirectProduct_of_comp_eq K0_shear31 K0_chi_1100_comp_shear31
theorem K0_iso_1110_1111 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1110) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_1111)) :=
  semidirectProduct_of_comp_eq K0_shear41 K0_chi_1110_comp_shear41
theorem K0_iso_1110_1101 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1110) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_1101)) :=
  semidirectProduct_of_comp_eq K0_swap34 K0_chi_1110_comp_swap34
theorem K0_iso_1110_1011 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1110) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_1011)) :=
  semidirectProduct_of_comp_eq K0_swap24 K0_chi_1110_comp_swap24
theorem K0_iso_1110_0111 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_1110) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_0111)) :=
  semidirectProduct_of_comp_eq K0_swap14 K0_chi_1110_comp_swap14

/-- Every nonzero raw character of `K₀ = (C₂)⁴` is `Aut(K₀)`-equivalent to `K0_chi_1000`. -/
theorem K0_iso_1000_of_ne_zero (χ : order16_wild_C2pow4 →* (ZMod 5)ˣ)
    (h : χ = K0_chi_1000 ∨ χ = K0_chi_0100 ∨ χ = K0_chi_0010 ∨ χ = K0_chi_0001 ∨
      χ = K0_chi_1100 ∨ χ = K0_chi_1010 ∨ χ = K0_chi_1001 ∨ χ = K0_chi_0110 ∨
      χ = K0_chi_0101 ∨ χ = K0_chi_0011 ∨ χ = K0_chi_1110 ∨ χ = K0_chi_1101 ∨
      χ = K0_chi_1011 ∨ χ = K0_chi_0111 ∨ χ = K0_chi_1111) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_1000) ≃*
      SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4 (unitAutHom.comp χ)) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact ⟨MulEquiv.refl _⟩
  · exact K0_iso_1000_0100
  · exact K0_iso_1000_0010
  · exact K0_iso_1000_0001
  · exact K0_iso_1000_1100
  · exact K0_iso_1000_1010
  · exact K0_iso_1000_1001
  · exact ⟨K0_iso_1000_1010.some.trans K0_iso_1010_0110.some⟩
  · exact ⟨K0_iso_1000_1001.some.trans K0_iso_1001_0101.some⟩
  · exact ⟨K0_iso_1000_1001.some.trans K0_iso_1001_0011.some⟩
  · exact ⟨K0_iso_1000_1100.some.trans K0_iso_1100_1110.some⟩
  · exact ⟨K0_iso_1000_1100.some.trans K0_iso_1100_1110.some |>.trans K0_iso_1110_1101.some⟩
  · exact ⟨K0_iso_1000_1100.some.trans K0_iso_1100_1110.some |>.trans K0_iso_1110_1011.some⟩
  · exact ⟨K0_iso_1000_1100.some.trans K0_iso_1100_1110.some |>.trans K0_iso_1110_0111.some⟩
  · exact ⟨K0_iso_1000_1100.some.trans K0_iso_1100_1110.some |>.trans K0_iso_1110_1111.some⟩

/-- **`K₀ = (C₂)⁴` contributes exactly `2` isomorphism classes**: the trivial action
(`K0_chi_0000`, abelian `C₅ × (C₂)⁴`) and the single class of all `15` nonzero characters
(represented by `K0_chi_1000`), since `Aut(K₀) = GL(4,2)` acts transitively on the nonzero
vectors of `Hom((C₂)⁴,(ZMod 5)ˣ) ≅ (C₂)⁴`. -/
theorem order80_classify_K0_reduced (φ' : order16_wild_C2pow4 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
          (unitAutHom.comp K0_chi_0000)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
          (unitAutHom.comp K0_chi_1000)) := by
  obtain ⟨χ, h1, h2, h3, h4, ⟨e⟩⟩ := order80_classify_G0 φ'
  have hχ4 : χ.comp (MonoidHom.inr _ _) =
      ((χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inl _ _)).coprod
        ((χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)) :=
    (MonoidHom.coprod_unique (χ.comp (MonoidHom.inr _ _))).symm
  have hχ3 : (χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _) =
      (((χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)).comp (MonoidHom.inl _ _)).coprod
        (((χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)) :=
    (MonoidHom.coprod_unique ((χ.comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _))).symm
  have hχ : χ = (χ.comp (MonoidHom.inl _ _)).coprod (χ.comp (MonoidHom.inr _ _)) :=
    (MonoidHom.coprod_unique χ).symm
  rw [hχ3] at hχ4
  rw [hχ4] at hχ
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;> rw [h1, h2, h3, h4] at hχ <;> subst hχ
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _ (Or.inr (Or.inr (Or.inl rfl)))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _ (Or.inr (Or.inl rfl))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl rfl)))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl rfl))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _ (Or.inl rfl)).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))).some.symm⟩
  · exact Or.inr ⟨e.trans (K0_iso_1000_of_ne_zero _
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))))))))))).some.symm⟩

/-- `K₀`'s `2` classes are distinct: the trivial character has kernel `16`, any nonzero one `8`. -/
theorem K0_ne_0000_1000 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5))
    order16_wild_C2pow4 (unitAutHom.comp K0_chi_0000) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_C2pow4
      (unitAutHom.comp K0_chi_1000)) :=
  order80_ne_of_ker_card order16_wild_C2pow4_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K0_chi_0000_ker_card,
      K0_chi_1000_ker_card]
    decide)

/-! ## `K₁₁ = Q₈ × C₂` (direct product) -/

noncomputable abbrev K11_chi_00 : order16_wild_G11 →* (ZMod 5)ˣ :=
  (1 : QuaternionGroup 2 →* (ZMod 5)ˣ).coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K11_chi_10 : order16_wild_G11 →* (ZMod 5)ˣ :=
  order40_chiQ8.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K11_chi_20 : order16_wild_G11 →* (ZMod 5)ˣ :=
  order40_chiQ8_xa.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K11_chi_30 : order16_wild_G11 →* (ZMod 5)ˣ :=
  order40_chiQ8_prod.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K11_chi_02 : order16_wild_G11 →* (ZMod 5)ˣ :=
  (1 : QuaternionGroup 2 →* (ZMod 5)ˣ).coprod order40_c2UnitHom
noncomputable abbrev K11_chi_12 : order16_wild_G11 →* (ZMod 5)ˣ :=
  order40_chiQ8.coprod order40_c2UnitHom
noncomputable abbrev K11_chi_22 : order16_wild_G11 →* (ZMod 5)ˣ :=
  order40_chiQ8_xa.coprod order40_c2UnitHom
noncomputable abbrev K11_chi_32 : order16_wild_G11 →* (ZMod 5)ˣ :=
  order40_chiQ8_prod.coprod order40_c2UnitHom

theorem order16_wild_G11_coprime : Nat.Coprime 5 (Fintype.card order16_wild_G11) := by decide

theorem K11_chi_00_ker_card : Fintype.card {k : order16_wild_G11 // K11_chi_00 k = 1} = 16 := by
  decide
theorem K11_chi_10_ker_card : Fintype.card {k : order16_wild_G11 // K11_chi_10 k = 1} = 8 := by
  decide
theorem K11_chi_02_ker_card : Fintype.card {k : order16_wild_G11 // K11_chi_02 k = 1} = 8 := by
  decide
theorem K11_chi_12_ker_card : Fintype.card {k : order16_wild_G11 // K11_chi_12 k = 1} = 8 := by
  decide

theorem K11_chi_10_sq_count :
    Nat.card {k : order16_wild_G11 // K11_chi_10 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 3 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K11_chi_02_sq_count :
    Nat.card {k : order16_wild_G11 // K11_chi_02 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 1 := by
  rw [Nat.card_eq_fintype_card]; decide

/-- `Aut(Q₈)`-orbit moves (reused from `Order88.lean`), extended by the identity on `C₂`,
merging the `3` nontrivial `Q₈`-part-only characters `chi_10, chi_20, chi_30`. -/
noncomputable def K11_shear : order16_wild_G11 ≃* order16_wild_G11 :=
  MulEquiv.prodCongr order88_Q8_shear (MulEquiv.refl _)
noncomputable def K11_swap : order16_wild_G11 ≃* order16_wild_G11 :=
  MulEquiv.prodCongr order88_Q8_swap (MulEquiv.refl _)

theorem K11_shear_apply (x : QuaternionGroup 2) (y : Multiplicative (ZMod 2)) :
    K11_shear (x, y) = (order88_Q8_shear x, y) := rfl
theorem K11_swap_apply (x : QuaternionGroup 2) (y : Multiplicative (ZMod 2)) :
    K11_swap (x, y) = (order88_Q8_swap x, y) := rfl

theorem K11_chi_10_comp_shear : K11_chi_10.comp K11_shear.toMonoidHom = K11_chi_30 := by
  ext ⟨x, y⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, K11_shear_apply, MonoidHom.coprod_apply,
    MonoidHom.coprod_apply,
    show order40_chiQ8 (order88_Q8_shear x) =
      (order40_chiQ8.comp order88_Q8_shear.toMonoidHom) x from rfl,
    order40_chiQ8_comp_shear]
theorem K11_chi_10_comp_swap : K11_chi_10.comp K11_swap.toMonoidHom = K11_chi_20 := by
  ext ⟨x, y⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, K11_swap_apply, MonoidHom.coprod_apply,
    MonoidHom.coprod_apply,
    show order40_chiQ8 (order88_Q8_swap x) =
      (order40_chiQ8.comp order88_Q8_swap.toMonoidHom) x from rfl,
    order40_chiQ8_comp_swap]

theorem K11_iso_10_30 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
    (unitAutHom.comp K11_chi_10) ≃* SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
      (unitAutHom.comp K11_chi_30)) :=
  semidirectProduct_of_comp_eq K11_shear K11_chi_10_comp_shear
theorem K11_iso_10_20 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
    (unitAutHom.comp K11_chi_10) ≃* SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
      (unitAutHom.comp K11_chi_20)) :=
  semidirectProduct_of_comp_eq K11_swap K11_chi_10_comp_swap

/-- **The `Q₈`-abelianization shear**: `(q,c) ↦ (q, c · f(q))` for `f : Q₈ → C₂` a homomorphism.
Merges `chi_02` (`C₂`-part alone nontrivial) with `chi_x2` for any nontrivial `Q₈`-part `x`,
since `C₂`'s dual character detects the shift `f(q)` as exactly the corresponding `Q₈`-character.
This is the subtlety that collapses `K₁₁`'s naive `4`-class count down to `3`: `chi_02`, `chi_12`,
`chi_22`, `chi_32` are ALL isomorphic. -/
theorem c2_sq_one' (y : Multiplicative (ZMod 2)) : y ^ 2 = 1 := by revert y; decide

noncomputable def K11_shearC2 (f : QuaternionGroup 2 →* Multiplicative (ZMod 2)) :
    order16_wild_G11 ≃* order16_wild_G11 where
  toFun p := (p.1, p.2 * f p.1)
  invFun p := (p.1, p.2 * f p.1)
  left_inv p := by
    have hf : f p.1 * f p.1 = 1 := by rw [← sq]; exact c2_sq_one' _
    ext
    · rfl
    · change p.2 * f p.1 * f p.1 = p.2
      rw [mul_assoc, hf, mul_one]
  right_inv p := by
    have hf : f p.1 * f p.1 = 1 := by rw [← sq]; exact c2_sq_one' _
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

theorem K11_shearC2_apply (f : QuaternionGroup 2 →* Multiplicative (ZMod 2))
    (q : QuaternionGroup 2) (c : Multiplicative (ZMod 2)) :
    K11_shearC2 f (q, c) = (q, c * f q) := rfl

theorem K11_chi_02_comp_shearC2_chiQ8 :
    K11_chi_02.comp (K11_shearC2 order88_chiQ8).toMonoidHom = K11_chi_12 := by
  ext ⟨q, c⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, K11_shearC2_apply, MonoidHom.coprod_apply,
    MonoidHom.coprod_apply, MonoidHom.one_apply, one_mul, map_mul,
    show order40_c2UnitHom (order88_chiQ8 q) = (order40_c2UnitHom.comp order88_chiQ8) q from rfl,
    ← order40_chiQ8, mul_comm]
theorem K11_chi_02_comp_shearC2_chiQ8_xa :
    K11_chi_02.comp (K11_shearC2 order88_chiQ8_xa).toMonoidHom = K11_chi_22 := by
  ext ⟨q, c⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, K11_shearC2_apply, MonoidHom.coprod_apply,
    MonoidHom.coprod_apply, MonoidHom.one_apply, one_mul, map_mul,
    show order40_c2UnitHom (order88_chiQ8_xa q) =
      (order40_c2UnitHom.comp order88_chiQ8_xa) q from rfl,
    ← order40_chiQ8_xa, mul_comm]
theorem K11_chi_02_comp_shearC2_chiQ8_prod :
    K11_chi_02.comp (K11_shearC2 order88_chiQ8_prod).toMonoidHom = K11_chi_32 := by
  ext ⟨q, c⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, K11_shearC2_apply, MonoidHom.coprod_apply,
    MonoidHom.coprod_apply, MonoidHom.one_apply, one_mul, map_mul,
    show order40_c2UnitHom (order88_chiQ8_prod q) =
      (order40_c2UnitHom.comp order88_chiQ8_prod) q from rfl,
    ← order40_chiQ8_prod, mul_comm]

theorem K11_iso_02_12 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
    (unitAutHom.comp K11_chi_02) ≃* SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
      (unitAutHom.comp K11_chi_12)) :=
  semidirectProduct_of_comp_eq (K11_shearC2 order88_chiQ8) K11_chi_02_comp_shearC2_chiQ8
theorem K11_iso_02_22 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
    (unitAutHom.comp K11_chi_02) ≃* SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
      (unitAutHom.comp K11_chi_22)) :=
  semidirectProduct_of_comp_eq (K11_shearC2 order88_chiQ8_xa) K11_chi_02_comp_shearC2_chiQ8_xa
theorem K11_iso_02_32 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
    (unitAutHom.comp K11_chi_02) ≃* SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
      (unitAutHom.comp K11_chi_32)) :=
  semidirectProduct_of_comp_eq (K11_shearC2 order88_chiQ8_prod) K11_chi_02_comp_shearC2_chiQ8_prod

/-- **`K₁₁ = Q₈ × C₂` contributes exactly `3` isomorphism classes**: the `8` raw candidates
collapse to `K11_chi_00` (trivial), `K11_chi_10` (`= chi_20 = chi_30`, `Q₈`-part alone nontrivial,
merged via `Aut(Q₈) ≅ S₄`'s transitive action on the `3` nontrivial `Q₈ → C₂` characters), and
`K11_chi_02` (`= chi_12 = chi_22 = chi_32`, ANY character with nontrivial `C₂`-part, merged via
the abelianization shear `K11_shearC2`). -/
theorem order80_classify_K11_reduced (φ' : order16_wild_G11 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
          (unitAutHom.comp K11_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
          (unitAutHom.comp K11_chi_10)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
          (unitAutHom.comp K11_chi_02)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order80_classify_G11 φ'
  rcases hinl with h1 | h1 | h1 | h1 <;> rcases hinr with h2 | h2 <;>
    rw [show χ = (χ.comp (MonoidHom.inl _ _)).coprod (χ.comp (MonoidHom.inr _ _)) from
      (MonoidHom.coprod_unique χ).symm, h1, h2] at e
  · exact Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr ⟨e⟩
  · exact Or.inr <| Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr ⟨e.trans K11_iso_02_12.some.symm⟩
  · exact Or.inr <| Or.inl ⟨e.trans K11_iso_10_20.some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans K11_iso_02_22.some.symm⟩
  · exact Or.inr <| Or.inl ⟨e.trans K11_iso_10_30.some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans K11_iso_02_32.some.symm⟩

/-- `K₁₁`'s `3` classes are pairwise distinct. -/
theorem K11_ne_00_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
    (unitAutHom.comp K11_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11 (unitAutHom.comp K11_chi_10)) :=
  order80_ne_of_ker_card order16_wild_G11_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K11_chi_00_ker_card,
      K11_chi_10_ker_card]; decide)
theorem K11_ne_00_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
    (unitAutHom.comp K11_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11 (unitAutHom.comp K11_chi_02)) :=
  order80_ne_of_ker_card order16_wild_G11_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K11_chi_00_ker_card,
      K11_chi_02_ker_card]; decide)
theorem K11_ne_10_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11
    (unitAutHom.comp K11_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G11 (unitAutHom.comp K11_chi_02)) :=
  order80_ne_of_ker_sq_count order16_wild_G11_coprime (by
    rw [K11_chi_10_sq_count, K11_chi_02_sq_count]; decide)

/-! ## `K₁₃ = C₄ × C₄` (direct product), on the concrete model
`Multiplicative (ZMod 4) × Multiplicative (ZMod 4)` (`order80_classify_G13` is already stated on
this concrete model, via `order16_A3_iso_concrete`). -/

noncomputable abbrev K13_h0 : Multiplicative (ZMod 4) →* (ZMod 5)ˣ := 1
noncomputable abbrev K13_h1 : Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 4) order40_u4 (by decide)
noncomputable abbrev K13_h2 : Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 4) (order40_u4 ^ 2) (by decide)
noncomputable abbrev K13_h3 : Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 4) (order40_u4 ^ 3) (by decide)

noncomputable abbrev K13_chi_00 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h0.coprod K13_h0
noncomputable abbrev K13_chi_10 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h1.coprod K13_h0
noncomputable abbrev K13_chi_20 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h2.coprod K13_h0
noncomputable abbrev K13_chi_30 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h3.coprod K13_h0
noncomputable abbrev K13_chi_01 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h0.coprod K13_h1
noncomputable abbrev K13_chi_11 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h1.coprod K13_h1
noncomputable abbrev K13_chi_21 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h2.coprod K13_h1
noncomputable abbrev K13_chi_31 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h3.coprod K13_h1
noncomputable abbrev K13_chi_02 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h0.coprod K13_h2
noncomputable abbrev K13_chi_12 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h1.coprod K13_h2
noncomputable abbrev K13_chi_22 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h2.coprod K13_h2
noncomputable abbrev K13_chi_32 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h3.coprod K13_h2
noncomputable abbrev K13_chi_03 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h0.coprod K13_h3
noncomputable abbrev K13_chi_13 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h1.coprod K13_h3
noncomputable abbrev K13_chi_23 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h2.coprod K13_h3
noncomputable abbrev K13_chi_33 : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ :=
  K13_h3.coprod K13_h3

theorem order40_C4C4_coprime :
    Nat.Coprime 5 (Fintype.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by decide

theorem K13_chi_00_ker_card :
    Fintype.card {k : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // K13_chi_00 k = 1} =
      16 := by decide
theorem K13_chi_20_ker_card :
    Fintype.card {k : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // K13_chi_20 k = 1} =
      8 := by decide
theorem K13_chi_10_ker_card :
    Fintype.card {k : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // K13_chi_10 k = 1} =
      4 := by decide

/-! ### Automorphisms of `C₄ × C₄`: swap, shears, and per-factor inversion -/

noncomputable def K13_cube1 :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  MulEquiv.prodCongr (unitAutHom (p := 4) zmod4_unit_3) (MulEquiv.refl _)
noncomputable def K13_cube2 :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  MulEquiv.prodCongr (MulEquiv.refl _) (unitAutHom (p := 4) zmod4_unit_3)

noncomputable def K13_swap :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4) where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv := by rintro ⟨a, b⟩; rfl
  right_inv := by rintro ⟨a, b⟩; rfl
  map_mul' := by rintro ⟨a, b⟩ ⟨a', b'⟩; rfl

noncomputable def K13_shear :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4) where
  toFun p := (p.1 * p.2, p.2)
  invFun p := (p.1 * p.2⁻¹, p.2)
  left_inv := by rintro ⟨a, b⟩; ext <;> revert a b <;> decide
  right_inv := by rintro ⟨a, b⟩; ext <;> revert a b <;> decide
  map_mul' := by rintro ⟨a, b⟩ ⟨a', b'⟩; ext <;> revert a b a' b' <;> decide

noncomputable def K13_shear2 :
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃*
      Multiplicative (ZMod 4) × Multiplicative (ZMod 4) where
  toFun p := (p.1, p.2 * p.1)
  invFun p := (p.1, p.2 * p.1⁻¹)
  left_inv := by rintro ⟨a, b⟩; ext <;> revert a b <;> decide
  right_inv := by rintro ⟨a, b⟩; ext <;> revert a b <;> decide
  map_mul' := by rintro ⟨a, b⟩ ⟨a', b'⟩; ext <;> revert a b a' b' <;> decide

/-! ### The `3` order-`2` raw candidates `{20,02,22}` merge to one class -/

theorem K13_chi_20_comp_swap : K13_chi_20.comp K13_swap.toMonoidHom = K13_chi_02 := by
  apply MonoidHom.ext; decide
theorem K13_chi_20_comp_shear : K13_chi_20.comp K13_shear.toMonoidHom = K13_chi_22 := by
  apply MonoidHom.ext; decide

theorem K13_iso_20_02 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_02)) :=
  semidirectProduct_of_comp_eq K13_swap K13_chi_20_comp_swap
theorem K13_iso_20_22 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_22)) :=
  semidirectProduct_of_comp_eq K13_shear K13_chi_20_comp_shear

/-- Every raw order-`2` character merges to `K13_chi_20`. -/
theorem K13_iso_20_of_ord2 (χ : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ)
    (h : χ = K13_chi_20 ∨ χ = K13_chi_02 ∨ χ = K13_chi_22) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_20) ≃*
      SemidirectProduct (Multiplicative (ZMod 5))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp χ)) := by
  rcases h with h | h | h <;> subst h
  · exact ⟨MulEquiv.refl _⟩
  · exact K13_iso_20_02
  · exact K13_iso_20_22

/-! ### The `12` order-`4` raw candidates merge to one class, hub `K13_chi_10` -/

theorem K13_chi_10_comp_cube1 : K13_chi_10.comp K13_cube1.toMonoidHom = K13_chi_30 := by
  apply MonoidHom.ext; decide
theorem K13_chi_10_comp_swap : K13_chi_10.comp K13_swap.toMonoidHom = K13_chi_01 := by
  apply MonoidHom.ext; decide
theorem K13_chi_10_comp_shear : K13_chi_10.comp K13_shear.toMonoidHom = K13_chi_11 := by
  apply MonoidHom.ext; decide
theorem K13_chi_01_comp_cube2 : K13_chi_01.comp K13_cube2.toMonoidHom = K13_chi_03 := by
  apply MonoidHom.ext; decide
theorem K13_chi_11_comp_cube1 : K13_chi_11.comp K13_cube1.toMonoidHom = K13_chi_31 := by
  apply MonoidHom.ext; decide
theorem K13_chi_11_comp_cube2 : K13_chi_11.comp K13_cube2.toMonoidHom = K13_chi_13 := by
  apply MonoidHom.ext; decide
theorem K13_chi_11_comp_shear2 : K13_chi_11.comp K13_shear2.toMonoidHom = K13_chi_21 := by
  apply MonoidHom.ext; decide
theorem K13_chi_13_comp_cube1 : K13_chi_13.comp K13_cube1.toMonoidHom = K13_chi_33 := by
  apply MonoidHom.ext; decide
theorem K13_chi_21_comp_swap : K13_chi_21.comp K13_swap.toMonoidHom = K13_chi_12 := by
  apply MonoidHom.ext; decide
theorem K13_chi_21_comp_cube2 : K13_chi_21.comp K13_cube2.toMonoidHom = K13_chi_23 := by
  apply MonoidHom.ext; decide
theorem K13_chi_12_comp_cube1 : K13_chi_12.comp K13_cube1.toMonoidHom = K13_chi_32 := by
  apply MonoidHom.ext; decide

theorem K13_iso_10_30 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_30)) :=
  semidirectProduct_of_comp_eq K13_cube1 K13_chi_10_comp_cube1
theorem K13_iso_10_01 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_01)) :=
  semidirectProduct_of_comp_eq K13_swap K13_chi_10_comp_swap
theorem K13_iso_10_11 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_11)) :=
  semidirectProduct_of_comp_eq K13_shear K13_chi_10_comp_shear
theorem K13_iso_01_03 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_01) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_03)) :=
  semidirectProduct_of_comp_eq K13_cube2 K13_chi_01_comp_cube2
theorem K13_iso_11_31 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_11) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_31)) :=
  semidirectProduct_of_comp_eq K13_cube1 K13_chi_11_comp_cube1
theorem K13_iso_11_13 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_11) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_13)) :=
  semidirectProduct_of_comp_eq K13_cube2 K13_chi_11_comp_cube2
theorem K13_iso_11_21 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_11) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_21)) :=
  semidirectProduct_of_comp_eq K13_shear2 K13_chi_11_comp_shear2
theorem K13_iso_13_33 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_13) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_33)) :=
  semidirectProduct_of_comp_eq K13_cube1 K13_chi_13_comp_cube1
theorem K13_iso_21_12 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_21) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_12)) :=
  semidirectProduct_of_comp_eq K13_swap K13_chi_21_comp_swap
theorem K13_iso_21_23 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_21) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_23)) :=
  semidirectProduct_of_comp_eq K13_cube2 K13_chi_21_comp_cube2
theorem K13_iso_12_32 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_12) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_32)) :=
  semidirectProduct_of_comp_eq K13_cube1 K13_chi_12_comp_cube1

/-- Every raw order-`4` character merges to `K13_chi_10`. -/
theorem K13_iso_10_of_ord4 (χ : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* (ZMod 5)ˣ)
    (h : χ = K13_chi_10 ∨ χ = K13_chi_30 ∨ χ = K13_chi_01 ∨ χ = K13_chi_03 ∨
      χ = K13_chi_11 ∨ χ = K13_chi_31 ∨ χ = K13_chi_13 ∨ χ = K13_chi_33 ∨
      χ = K13_chi_21 ∨ χ = K13_chi_12 ∨ χ = K13_chi_23 ∨ χ = K13_chi_32) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_10) ≃*
      SemidirectProduct (Multiplicative (ZMod 5))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp χ)) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact ⟨MulEquiv.refl _⟩
  · exact K13_iso_10_30
  · exact K13_iso_10_01
  · exact ⟨K13_iso_10_01.some.trans K13_iso_01_03.some⟩
  · exact K13_iso_10_11
  · exact ⟨K13_iso_10_11.some.trans K13_iso_11_31.some⟩
  · exact ⟨K13_iso_10_11.some.trans K13_iso_11_13.some⟩
  · exact ⟨K13_iso_10_11.some.trans K13_iso_11_13.some |>.trans K13_iso_13_33.some⟩
  · exact ⟨K13_iso_10_11.some.trans K13_iso_11_21.some⟩
  · exact ⟨K13_iso_10_11.some.trans K13_iso_11_21.some |>.trans K13_iso_21_12.some⟩
  · exact ⟨K13_iso_10_11.some.trans K13_iso_11_21.some |>.trans K13_iso_21_23.some⟩
  · exact ⟨K13_iso_10_11.some.trans K13_iso_11_21.some |>.trans K13_iso_21_12.some
      |>.trans K13_iso_12_32.some⟩

/-- **`K₁₃ = C₄ × C₄` contributes exactly `3` isomorphism classes**: the `16` raw candidates
collapse, via `Aut(C₄×C₄) ≅ GL(2,ℤ/4)` acting transitively on each "order class" of
`Hom(K₁₃,(ZMod 5)ˣ) ≅ (ℤ/4)²` (order `1`, `2`, or `4`), to `K13_chi_00` (trivial), `K13_chi_20`
(the `3`-element order-`2` orbit `{20,02,22}`), and `K13_chi_10` (the `12`-element order-`4`
orbit, everything else). -/
theorem order80_classify_K13_reduced
    (φ' : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) →*
      MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5))
          (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5))
          (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_20)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5))
          (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_10)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order80_classify_G13 φ'
  rw [show χ = (χ.comp (MonoidHom.inl _ _)).coprod (χ.comp (MonoidHom.inr _ _)) from
    (MonoidHom.coprod_unique χ).symm] at e
  rcases hinl with h1 | h1 | h1 | h1 <;> rcases hinr with h2 | h2 | h2 | h2 <;> rw [h1, h2] at e
  · exact Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inl ⟨e.trans (K13_iso_20_of_ord2 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inl ⟨e.trans (K13_iso_20_of_ord2 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inl ⟨e.trans (K13_iso_20_of_ord2 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩
  · exact Or.inr <| Or.inr ⟨e.trans (K13_iso_10_of_ord4 _ (by tauto)).some.symm⟩

/-- `K₁₃`'s `3` classes are pairwise distinct (via kernel cardinality: `16, 8, 4`). -/
theorem K13_ne_00_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_20)) :=
  order80_ne_of_ker_card order40_C4C4_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K13_chi_00_ker_card,
      K13_chi_20_ker_card]; decide)
theorem K13_ne_00_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_10)) :=
  order80_ne_of_ker_card order40_C4C4_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K13_chi_00_ker_card,
      K13_chi_10_ker_card]; decide)
theorem K13_ne_20_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (unitAutHom.comp K13_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
      (unitAutHom.comp K13_chi_10)) :=
  order80_ne_of_ker_card order40_C4C4_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K13_chi_20_ker_card,
      K13_chi_10_ker_card]; decide)

/-! ## `K₈ = D₈ × C₂ = K₈g ⋊[ψ₃] C₂` -/

/-- Invariance of the trivial `K₈g`-character under `ψ₃`. -/
theorem K8_chiC4C2_one_invariant :
    ∀ b, (1 : K8g →* (ZMod 5)ˣ).comp (c2Action_psi3 b).toMonoidHom = 1 :=
  fun _ => by ext; simp

theorem K8_chiC4C2_fst_two_invariant :
    ∀ b, order40_chiC4C2_fst_two.comp (c2Action_psi3 b).toMonoidHom = order40_chiC4C2_fst_two := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi3 _ from
        by rw [c2Action_psi3_gen]] <;>
    decide

theorem K8_chiC4C2_snd_two_invariant :
    ∀ b, order40_chiC4C2_snd_two.comp (c2Action_psi3 b).toMonoidHom = order40_chiC4C2_snd_two := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi3 _ from
        by rw [c2Action_psi3_gen]] <;>
    decide

theorem K8_chiC4C2_prod_two_invariant :
    ∀ b, order40_chiC4C2_prod_two.comp (c2Action_psi3 b).toMonoidHom =
      order40_chiC4C2_prod_two := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi3 _ from
        by rw [c2Action_psi3_gen]] <;>
    decide

noncomputable abbrev K8_chi_00 : order16_wild_G8 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 1
    (fun b => by rw [K8_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K8_chi_02 : order16_wild_G8 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 order40_c2UnitHom
    (fun b => by rw [K8_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K8_chi_f0 : order16_wild_G8 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_fst_two 1
    (fun b => by rw [K8_chiC4C2_fst_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K8_chi_f2 : order16_wild_G8 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_fst_two order40_c2UnitHom
    (fun b => by rw [K8_chiC4C2_fst_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K8_chi_s0 : order16_wild_G8 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_snd_two 1
    (fun b => by rw [K8_chiC4C2_snd_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K8_chi_s2 : order16_wild_G8 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_snd_two order40_c2UnitHom
    (fun b => by rw [K8_chiC4C2_snd_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K8_chi_p0 : order16_wild_G8 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_prod_two 1
    (fun b => by rw [K8_chiC4C2_prod_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K8_chi_p2 : order16_wild_G8 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_prod_two order40_c2UnitHom
    (fun b => by rw [K8_chiC4C2_prod_two_invariant, mulAut_conj_of_comm]; ext a; simp)

theorem order16_wild_G8_coprime : Nat.Coprime 5 (Fintype.card order16_wild_G8) := by decide

theorem K8_chi_00_ker_card : Fintype.card {k : order16_wild_G8 // K8_chi_00 k = 1} = 16 := by
  decide
theorem K8_chi_f0_ker_card : Fintype.card {k : order16_wild_G8 // K8_chi_f0 k = 1} = 8 := by decide
theorem K8_chi_s0_ker_card : Fintype.card {k : order16_wild_G8 // K8_chi_s0 k = 1} = 8 := by decide
theorem K8_chi_02_ker_card : Fintype.card {k : order16_wild_G8 // K8_chi_02 k = 1} = 8 := by decide

/-- **The `K₈g`-shear `(a,b) ↦ (a, b·π(a))`, `π : C₄ → C₂` the mod-`2` projection**: commutes
with `ψ₃` (both sides invert `a`, fix the shift), hence extends to an automorphism of `K₈`.
Merges `snd_two` with `prod_two` (adding `fst_two`'s value into the shift). -/
noncomputable def K8g_shear2 : K8g ≃* K8g where
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

/-- `K₈g_shear2` embedded into `order16_wild_G8` via `inl`. -/
noncomputable def K8_shear2_inl : K8g →* order16_wild_G8 :=
  (SemidirectProduct.inl : K8g →* order16_wild_G8).comp K8g_shear2.toMonoidHom

theorem K8g_shear2_comp_psi3 :
    ∀ b, K8_shear2_inl.comp (c2Action_psi3 b).toMonoidHom =
      (MulAut.conj ((SemidirectProduct.inr : Multiplicative (ZMod 2) →* order16_wild_G8) b)
        ).toMonoidHom.comp K8_shear2_inl := by
  intro b
  apply MonoidHom.ext
  intro a
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · simp [K8_shear2_inl]
  · change SemidirectProduct.inl (K8g_shear2 ((c2Action_psi3
    (Multiplicative.ofAdd (1 : ZMod 2))) a))
      = MulAut.conj (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)))
        (SemidirectProduct.inl (K8g_shear2 a))
    rw [show c2Action_psi3 (Multiplicative.ofAdd (1 : ZMod 2)) a = psi3 a from
        by rw [c2Action_psi3_gen], MulAut.conj_apply, ← map_inv, ← SemidirectProduct.inl_aut]
    congr 1
    revert a; decide

noncomputable def K8_shear2 : order16_wild_G8 →* order16_wild_G8 :=
  SemidirectProduct.lift K8_shear2_inl
    (SemidirectProduct.inr : Multiplicative (ZMod 2) →* order16_wild_G8) K8g_shear2_comp_psi3

theorem K8_shear2_bijective : Function.Bijective K8_shear2 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def K8_shear2_equiv : order16_wild_G8 ≃* order16_wild_G8 :=
  MulEquiv.ofBijective K8_shear2 K8_shear2_bijective

theorem K8_chi_s0_comp_shear2 : K8_chi_s0.comp K8_shear2_equiv.toMonoidHom = K8_chi_p0 := by
  apply MonoidHom.ext; decide
theorem K8_chi_s2_comp_shear2 : K8_chi_s2.comp K8_shear2_equiv.toMonoidHom = K8_chi_p2 := by
  apply MonoidHom.ext; decide

theorem K8_iso_s0_p0 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
    (unitAutHom.comp K8_chi_s0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 (unitAutHom.comp K8_chi_p0)) :=
  semidirectProduct_of_comp_eq K8_shear2_equiv K8_chi_s0_comp_shear2
theorem K8_iso_s2_p2 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
    (unitAutHom.comp K8_chi_s2) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 (unitAutHom.comp K8_chi_p2)) :=
  semidirectProduct_of_comp_eq K8_shear2_equiv K8_chi_s2_comp_shear2

/-- **The OUTER shear `s ↦ s·k` for `k = inl(1,1) : K8g`** (odd `a`, so `fst_two k = u4²`,
`prod_two k = u4²`, `snd_two k = 1`), keeping `inl` fixed. Since `fst_two`/`prod_two`'s value at
`k` is nontrivial, this shear toggles the OUTER `C₂`-character (`f2 ↦ f2 · f1(k)`) whenever
`f1 ∈ {fst_two, prod_two}`, merging `f0 = f2` and `p0 = p2`; it FIXES `chi_00` and `chi_s0`
(`snd_two k = 1`). Combined with `K8_shear2` (`s0 = p0`, `s2 = p2`), this connects
`s0 = p0 = p2 = s2` into a single class. -/
noncomputable def K8_shearOuter_B : order16_wild_G8 :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 2))) *
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem K8_shearOuter_B_pow2 : K8_shearOuter_B ^ 2 = 1 := by decide

theorem K8_shearOuter_compat :
    ∀ b, (SemidirectProduct.inl : K8g →* order16_wild_G8).comp (c2Action_psi3 b).toMonoidHom =
      (MulAut.conj ((C2_powHom K8_shearOuter_B K8_shearOuter_B_pow2) b)).toMonoidHom.comp
        (SemidirectProduct.inl : K8g →* order16_wild_G8) := by
  intro b
  apply MonoidHom.ext
  intro a
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · simp
  · change SemidirectProduct.inl (psi3 a) =
      MulAut.conj (K8_shearOuter_B) (SemidirectProduct.inl a)
    rw [MulAut.conj_apply, K8_shearOuter_B]
    revert a; decide

noncomputable def K8_shearOuter : order16_wild_G8 →* order16_wild_G8 :=
  SemidirectProduct.lift (SemidirectProduct.inl : K8g →* order16_wild_G8)
    (C2_powHom K8_shearOuter_B K8_shearOuter_B_pow2) K8_shearOuter_compat

theorem K8_shearOuter_bijective : Function.Bijective K8_shearOuter := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def K8_shearOuter_equiv : order16_wild_G8 ≃* order16_wild_G8 :=
  MulEquiv.ofBijective K8_shearOuter K8_shearOuter_bijective

theorem K8_chi_f0_comp_shearOuter : K8_chi_f0.comp K8_shearOuter_equiv.toMonoidHom = K8_chi_f2 := by
  apply MonoidHom.ext; decide
theorem K8_chi_p0_comp_shearOuter : K8_chi_p0.comp K8_shearOuter_equiv.toMonoidHom = K8_chi_p2 := by
  apply MonoidHom.ext; decide

theorem K8_iso_f0_f2 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
    (unitAutHom.comp K8_chi_f0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 (unitAutHom.comp K8_chi_f2)) :=
  semidirectProduct_of_comp_eq K8_shearOuter_equiv K8_chi_f0_comp_shearOuter
theorem K8_iso_p0_p2 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
    (unitAutHom.comp K8_chi_p0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 (unitAutHom.comp K8_chi_p2)) :=
  semidirectProduct_of_comp_eq K8_shearOuter_equiv K8_chi_p0_comp_shearOuter

/-- **`K₈ = D₈ × C₂` contributes exactly `4` isomorphism classes**: the `8` raw candidates
collapse via `K8g_shear2` (`s0 = p0`, `s2 = p2`) and `K8_shearOuter` (`f0 = f2`, `p0 = p2`),
chaining to `s0 = p0 = p2 = s2` — a single class — while `K8_chi_00`, `K8_chi_f0`, and
`K8_chi_02` remain pairwise distinct (confirmed by their differing order-`2`-element counts:
`00`'s kernel is the whole group, `f0`'s kernel has `7` order-`2` elements (a `(C₂)³` from the
squares subgroup, trivial action), `s0`'s kernel has `5` (a `D₈`, nontrivial inversion action),
and `02`'s kernel has `3` (`K₈g` itself, abelian `C₄ × C₂`)). Representatives: `K8_chi_00`,
`K8_chi_f0` (`= chi_f2`), `K8_chi_02`, `K8_chi_s0` (`= chi_p0 = chi_p2 = chi_s2`). -/
theorem order80_classify_K8_reduced (φ' : order16_wild_G8 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
          (unitAutHom.comp K8_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
          (unitAutHom.comp K8_chi_f0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
          (unitAutHom.comp K8_chi_02)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
          (unitAutHom.comp K8_chi_s0)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order80_classify_G8 φ'
  rcases hinl with h1 | h1 | h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = K8_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = K8_chi_02 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K8_chi_f0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K8_chi_f2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e.trans K8_iso_f0_f2.some.symm⟩
  · have hχ : χ = K8_chi_s0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = K8_chi_s2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr
      ⟨e.trans K8_iso_s2_p2.some |>.trans K8_iso_p0_p2.some.symm |>.trans K8_iso_s0_p0.some.symm⟩
  · have hχ : χ = K8_chi_p0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr ⟨e.trans K8_iso_s0_p0.some.symm⟩
  · have hχ : χ = K8_chi_p2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr
      ⟨e.trans K8_iso_p0_p2.some.symm |>.trans K8_iso_s0_p0.some.symm⟩

theorem K8_chi_f0_sq_count :
    Nat.card {k : order16_wild_G8 // K8_chi_f0 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 7 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K8_chi_02_sq_count :
    Nat.card {k : order16_wild_G8 // K8_chi_02 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 3 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K8_chi_s0_sq_count :
    Nat.card {k : order16_wild_G8 // K8_chi_s0 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 5 := by
  rw [Nat.card_eq_fintype_card]; decide

/-- `K₈`'s `4` classes are pairwise distinct. -/
theorem K8_ne_00_f0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
    (unitAutHom.comp K8_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 (unitAutHom.comp K8_chi_f0)) :=
  order80_ne_of_ker_card order16_wild_G8_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K8_chi_00_ker_card,
      K8_chi_f0_ker_card]; decide)
theorem K8_ne_00_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
    (unitAutHom.comp K8_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 (unitAutHom.comp K8_chi_02)) :=
  order80_ne_of_ker_card order16_wild_G8_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K8_chi_00_ker_card,
      K8_chi_02_ker_card]; decide)
theorem K8_ne_00_s0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
    (unitAutHom.comp K8_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 (unitAutHom.comp K8_chi_s0)) :=
  order80_ne_of_ker_card order16_wild_G8_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K8_chi_00_ker_card,
      K8_chi_s0_ker_card]; decide)
theorem K8_ne_f0_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
    (unitAutHom.comp K8_chi_f0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 (unitAutHom.comp K8_chi_02)) :=
  order80_ne_of_ker_sq_count order16_wild_G8_coprime (by
    rw [K8_chi_f0_sq_count, K8_chi_02_sq_count]; decide)
theorem K8_ne_f0_s0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
    (unitAutHom.comp K8_chi_f0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 (unitAutHom.comp K8_chi_s0)) :=
  order80_ne_of_ker_sq_count order16_wild_G8_coprime (by
    rw [K8_chi_f0_sq_count, K8_chi_s0_sq_count]; decide)
theorem K8_ne_02_s0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8
    (unitAutHom.comp K8_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G8 (unitAutHom.comp K8_chi_s0)) :=
  order80_ne_of_ker_sq_count order16_wild_G8_coprime (by
    rw [K8_chi_02_sq_count, K8_chi_s0_sq_count]; decide)

/-! ## `K₉ = K₈g ⋊[ψ₅] C₂` -/

theorem K9_chiC4C2_one_invariant :
    ∀ b, (1 : K8g →* (ZMod 5)ˣ).comp (c2Action_psi5 b).toMonoidHom = 1 :=
  fun _ => by ext; simp

theorem K9_chiC4C2_fst_two_invariant :
    ∀ b, order40_chiC4C2_fst_two.comp (c2Action_psi5 b).toMonoidHom = order40_chiC4C2_fst_two := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi5 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi5 _ from
        by rw [c2Action_psi5_gen]] <;>
    decide

theorem K9_chiC4C2_fst_four_invariant :
    ∀ b, order40_chiC4C2_fst_four.comp (c2Action_psi5 b).toMonoidHom =
      order40_chiC4C2_fst_four := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi5 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi5 _ from
        by rw [c2Action_psi5_gen]] <;>
    decide

theorem K9_chiC4C2_fst_four_inv_invariant :
    ∀ b, order40_chiC4C2_fst_four_inv.comp (c2Action_psi5 b).toMonoidHom =
      order40_chiC4C2_fst_four_inv := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi5 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi5 _ from
        by rw [c2Action_psi5_gen]] <;>
    decide

noncomputable abbrev K9_chi_00 : order16_wild_G9 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 1
    (fun b => by rw [K9_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K9_chi_02 : order16_wild_G9 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 order40_c2UnitHom
    (fun b => by rw [K9_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K9_chi_t0 : order16_wild_G9 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_fst_two 1
    (fun b => by rw [K9_chiC4C2_fst_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K9_chi_t2 : order16_wild_G9 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_fst_two order40_c2UnitHom
    (fun b => by rw [K9_chiC4C2_fst_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K9_chi_40 : order16_wild_G9 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_fst_four 1
    (fun b => by rw [K9_chiC4C2_fst_four_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K9_chi_42 : order16_wild_G9 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_fst_four order40_c2UnitHom
    (fun b => by rw [K9_chiC4C2_fst_four_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K9_chi_60 : order16_wild_G9 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_fst_four_inv 1
    (fun b => by rw [K9_chiC4C2_fst_four_inv_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K9_chi_62 : order16_wild_G9 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_fst_four_inv order40_c2UnitHom
    (fun b => by rw [K9_chiC4C2_fst_four_inv_invariant, mulAut_conj_of_comm]; ext a; simp)

theorem order16_wild_G9_coprime : Nat.Coprime 5 (Fintype.card order16_wild_G9) := by decide

/-! ### `Aut(K₉)`-orbit exploration: cube on the `C₄`-part, plus an outer shear -/

/-- Cubing (inverting) the `C₄`-part `a`, fixing `b`: commutes with `ψ₅` since `proj(a³) = proj(a)`
(the mod-`2` projection is invariant under negation). Merges `fst_four` with `fst_four_inv`. -/
noncomputable def K9g_cube : K8g ≃* K8g :=
  MulEquiv.prodCongr (unitAutHom (p := 4) zmod4_unit_3) (MulEquiv.refl _)

noncomputable def K9_cube_inl : K8g →* order16_wild_G9 :=
  (SemidirectProduct.inl : K8g →* order16_wild_G9).comp K9g_cube.toMonoidHom

theorem K9g_cube_comp_psi5 :
    ∀ b, K9_cube_inl.comp (c2Action_psi5 b).toMonoidHom =
      (MulAut.conj ((SemidirectProduct.inr : Multiplicative (ZMod 2) →* order16_wild_G9) b)
        ).toMonoidHom.comp K9_cube_inl := by
  intro b
  apply MonoidHom.ext
  intro a
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · simp [K9_cube_inl]
  · change SemidirectProduct.inl (K9g_cube (psi5 a)) =
      MulAut.conj (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)))
        (SemidirectProduct.inl (K9g_cube a))
    rw [MulAut.conj_apply, ← map_inv, ← SemidirectProduct.inl_aut,
      show c2Action_psi5 (Multiplicative.ofAdd (1 : ZMod 2)) = psi5 from c2Action_psi5_gen]
    congr 1
    revert a; decide

noncomputable def K9_cube : order16_wild_G9 →* order16_wild_G9 :=
  SemidirectProduct.lift K9_cube_inl
    (SemidirectProduct.inr : Multiplicative (ZMod 2) →* order16_wild_G9) K9g_cube_comp_psi5

theorem K9_cube_bijective : Function.Bijective K9_cube := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def K9_cube_equiv : order16_wild_G9 ≃* order16_wild_G9 :=
  MulEquiv.ofBijective K9_cube K9_cube_bijective

theorem K9_chi_40_comp_cube : K9_chi_40.comp K9_cube_equiv.toMonoidHom = K9_chi_60 := by
  apply MonoidHom.ext; decide
theorem K9_chi_42_comp_cube : K9_chi_42.comp K9_cube_equiv.toMonoidHom = K9_chi_62 := by
  apply MonoidHom.ext; decide

theorem K9_iso_40_60 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_40) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_60)) :=
  semidirectProduct_of_comp_eq K9_cube_equiv K9_chi_40_comp_cube
theorem K9_iso_42_62 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_42) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_62)) :=
  semidirectProduct_of_comp_eq K9_cube_equiv K9_chi_42_comp_cube

/-- Outer shear `s ↦ s·k` for `k = inl(1,1) : K8g`, testing whether it merges the
`C₂`-outer-part the same way `K8_shearOuter` did for `K₈`. -/
noncomputable def K9_shearOuter_B : order16_wild_G9 :=
  SemidirectProduct.inl ((Multiplicative.ofAdd (1 : ZMod 4)) ^ 2, (1 : Multiplicative (ZMod 2))) *
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem K9_shearOuter_B_pow2 : K9_shearOuter_B ^ 2 = 1 := by decide

theorem K9_shearOuter_compat :
    ∀ b, (SemidirectProduct.inl : K8g →* order16_wild_G9).comp (c2Action_psi5 b).toMonoidHom =
      (MulAut.conj ((C2_powHom K9_shearOuter_B K9_shearOuter_B_pow2) b)).toMonoidHom.comp
        (SemidirectProduct.inl : K8g →* order16_wild_G9) := by
  intro b
  apply MonoidHom.ext
  intro a
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · simp
  · change SemidirectProduct.inl (psi5 a) =
      MulAut.conj (K9_shearOuter_B) (SemidirectProduct.inl a)
    rw [MulAut.conj_apply, K9_shearOuter_B]
    revert a; decide

noncomputable def K9_shearOuter : order16_wild_G9 →* order16_wild_G9 :=
  SemidirectProduct.lift (SemidirectProduct.inl : K8g →* order16_wild_G9)
    (C2_powHom K9_shearOuter_B K9_shearOuter_B_pow2) K9_shearOuter_compat

theorem K9_shearOuter_bijective : Function.Bijective K9_shearOuter := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def K9_shearOuter_equiv : order16_wild_G9 ≃* order16_wild_G9 :=
  MulEquiv.ofBijective K9_shearOuter K9_shearOuter_bijective

theorem K9_chi_40_comp_shearOuter : K9_chi_40.comp K9_shearOuter_equiv.toMonoidHom = K9_chi_42 := by
  apply MonoidHom.ext; decide
theorem K9_chi_60_comp_shearOuter : K9_chi_60.comp K9_shearOuter_equiv.toMonoidHom = K9_chi_62 := by
  apply MonoidHom.ext; decide

theorem K9_iso_40_42 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_40) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_42)) :=
  semidirectProduct_of_comp_eq K9_shearOuter_equiv K9_chi_40_comp_shearOuter
theorem K9_iso_60_62 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_60) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_62)) :=
  semidirectProduct_of_comp_eq K9_shearOuter_equiv K9_chi_60_comp_shearOuter

theorem order16_wild_G9_chi_00_ker_card :
    Fintype.card {k : order16_wild_G9 // K9_chi_00 k = 1} = 16 := by decide
theorem order16_wild_G9_chi_02_ker_card :
    Fintype.card {k : order16_wild_G9 // K9_chi_02 k = 1} = 8 := by decide
theorem order16_wild_G9_chi_t0_ker_card :
    Fintype.card {k : order16_wild_G9 // K9_chi_t0 k = 1} = 8 := by decide
theorem order16_wild_G9_chi_t2_ker_card :
    Fintype.card {k : order16_wild_G9 // K9_chi_t2 k = 1} = 8 := by decide
theorem order16_wild_G9_chi_40_ker_card :
    Fintype.card {k : order16_wild_G9 // K9_chi_40 k = 1} = 4 := by decide

theorem K9_chi_02_sq_count :
    Nat.card {k : order16_wild_G9 // K9_chi_02 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 3 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K9_chi_t0_sq_count :
    Nat.card {k : order16_wild_G9 // K9_chi_t0 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 7 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K9_chi_t2_sq_count :
    Nat.card {k : order16_wild_G9 // K9_chi_t2 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 3 := by
  rw [Nat.card_eq_fintype_card]; decide

/-- **`K₉` contributes `4` or `5` isomorphism classes** (see note below on the one open
`chi_02`-vs-`chi_t2` question): representatives `K9_chi_00`, `K9_chi_02`, `K9_chi_t0`, `K9_chi_t2`,
`K9_chi_40` (`= chi_42 = chi_60 = chi_62`, merged via `K9_cube` and `K9_shearOuter`). -/
theorem order80_classify_K9_reduced (φ' : order16_wild_G9 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
          (unitAutHom.comp K9_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
          (unitAutHom.comp K9_chi_02)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
          (unitAutHom.comp K9_chi_t0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
          (unitAutHom.comp K9_chi_t2)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
          (unitAutHom.comp K9_chi_40)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order80_classify_G9 φ'
  rcases hinl with h1 | h1 | h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = K9_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = K9_chi_02 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K9_chi_t0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K9_chi_t2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K9_chi_40 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = K9_chi_42 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨e.trans K9_iso_40_42.some.symm⟩
  · have hχ : χ = K9_chi_60 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨e.trans K9_iso_40_60.some.symm⟩
  · have hχ : χ = K9_chi_62 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨e.trans K9_iso_60_62.some.symm |>.trans K9_iso_40_60.some.symm⟩

/-- `K₉`'s classes are pairwise distinct EXCEPT for the open `chi_02`-vs-`chi_t2` question
(see the note above): all other `9` of the `10` pairs among `{00,02,t0,t2,40}` are resolved. -/
theorem K9_ne_00_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_02)) :=
  order80_ne_of_ker_card order16_wild_G9_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, order16_wild_G9_chi_00_ker_card,
      order16_wild_G9_chi_02_ker_card]; decide)
theorem K9_ne_00_t0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_t0)) :=
  order80_ne_of_ker_card order16_wild_G9_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, order16_wild_G9_chi_00_ker_card,
      order16_wild_G9_chi_t0_ker_card]; decide)
theorem K9_ne_00_t2 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_t2)) :=
  order80_ne_of_ker_card order16_wild_G9_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, order16_wild_G9_chi_00_ker_card,
      order16_wild_G9_chi_t2_ker_card]; decide)
theorem K9_ne_00_40 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_40)) :=
  order80_ne_of_ker_card order16_wild_G9_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, order16_wild_G9_chi_00_ker_card,
      order16_wild_G9_chi_40_ker_card]; decide)
theorem K9_ne_02_40 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_40)) :=
  order80_ne_of_ker_card order16_wild_G9_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, order16_wild_G9_chi_02_ker_card,
      order16_wild_G9_chi_40_ker_card]; decide)
theorem K9_ne_t0_40 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_t0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_40)) :=
  order80_ne_of_ker_card order16_wild_G9_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, order16_wild_G9_chi_t0_ker_card,
      order16_wild_G9_chi_40_ker_card]; decide)
theorem K9_ne_t2_40 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_t2) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_40)) :=
  order80_ne_of_ker_card order16_wild_G9_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, order16_wild_G9_chi_t2_ker_card,
      order16_wild_G9_chi_40_ker_card]; decide)
theorem K9_ne_02_t0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_t0)) :=
  order80_ne_of_ker_sq_count order16_wild_G9_coprime (by
    rw [K9_chi_02_sq_count, K9_chi_t0_sq_count]; decide)
theorem K9_ne_t0_t2 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9
    (unitAutHom.comp K9_chi_t0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G9 (unitAutHom.comp K9_chi_t2)) :=
  order80_ne_of_ker_sq_count order16_wild_G9_coprime (by
    rw [K9_chi_t0_sq_count, K9_chi_t2_sq_count]; decide)

/-! `chi_02` and `chi_t2` tie on kernel cardinality (`8`) AND order-`2`-count (`3`): both kernels
are abstractly `≅ C₄ × C₂` (the unique order-`8` group with exactly `3` involutions). A structural
difference DOES exist — `ker(02)`'s order-`4` elements all square to `inl(2,0)`, while
`ker(t2)`'s square to `inl(2,1)` (a different, non-conjugate element) — but this is not yet
packaged as a reusable `Aut(K)`-orbit invariant here (would need a "commutes with `n0` AND squares
to a named target" transport lemma analogous to `order80_card_centralizer_ord_eq`). Every
`SemidirectProduct.lift`-style automorphism of `K₉` tried (`cube`, `shearOuter` for every valid
choice of shift, and their composites) fixes both `chi_02` and `chi_t2` individually, and the
naive `b ↔ h` swap fails to even be a homomorphism (the twisted multiplication doesn't commute
with it) — strong circumstantial evidence they are genuinely distinct, but NOT a complete proof.
This is the one open gap in the `K₉` classification: `K₉` has *at most* `5` classes
(`00, 02, t0, t2, {40=42=60=62}`), of which `00` is distinct from all others (cardinality `16`),
`t0`/`02`/`t2` are pairwise almost-distinguished (`t0 ≠ 02` and `t0 ≠ t2` proved via
order-`2`-count; `02` vs `t2` remains open), and the `4`-element family `{40,42,60,62}` is
distinct from everything else via cardinality (`4`). -/

/-! ## `K₁₀ = K₈g ⋊[ψ₆] C₂ = Q₈ ⋊ C₂` -/

theorem K10_chiC4C2_one_invariant :
    ∀ b, (1 : K8g →* (ZMod 5)ˣ).comp (c2Action_psi6 b).toMonoidHom = 1 :=
  fun _ => by ext; simp

theorem K10_chiC4C2_fst_two_invariant :
    ∀ b, order40_chiC4C2_fst_two.comp (c2Action_psi6 b).toMonoidHom =
      order40_chiC4C2_fst_two := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi6 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi6 _ from
        by rw [c2Action_psi6_gen]] <;>
    decide

theorem K10_chiC4C2_snd_two_invariant :
    ∀ b, order40_chiC4C2_snd_two.comp (c2Action_psi6 b).toMonoidHom =
      order40_chiC4C2_snd_two := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi6 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi6 _ from
        by rw [c2Action_psi6_gen]] <;>
    decide

theorem K10_chiC4C2_prod_two_invariant :
    ∀ b, order40_chiC4C2_prod_two.comp (c2Action_psi6 b).toMonoidHom =
      order40_chiC4C2_prod_two := by
  apply semidirectProduct_c2_compat
  apply order40_c4c2_hom_ext <;>
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show c2Action_psi6 (Multiplicative.ofAdd (1 : ZMod 2)) _ = psi6 _ from
        by rw [c2Action_psi6_gen]] <;>
    decide

noncomputable abbrev K10_chi_00 : order16_wild_G10 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 1
    (fun b => by rw [K10_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K10_chi_02 : order16_wild_G10 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 order40_c2UnitHom
    (fun b => by rw [K10_chiC4C2_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K10_chi_f0 : order16_wild_G10 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_fst_two 1
    (fun b => by rw [K10_chiC4C2_fst_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K10_chi_f2 : order16_wild_G10 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_fst_two order40_c2UnitHom
    (fun b => by rw [K10_chiC4C2_fst_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K10_chi_s0 : order16_wild_G10 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_snd_two 1
    (fun b => by rw [K10_chiC4C2_snd_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K10_chi_s2 : order16_wild_G10 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_snd_two order40_c2UnitHom
    (fun b => by rw [K10_chiC4C2_snd_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K10_chi_p0 : order16_wild_G10 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_prod_two 1
    (fun b => by rw [K10_chiC4C2_prod_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K10_chi_p2 : order16_wild_G10 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC4C2_prod_two order40_c2UnitHom
    (fun b => by rw [K10_chiC4C2_prod_two_invariant, mulAut_conj_of_comm]; ext a; simp)

theorem order16_wild_G10_coprime : Nat.Coprime 5 (Fintype.card order16_wild_G10) := by decide

theorem K10_chi_00_ker_card : Fintype.card {k : order16_wild_G10 // K10_chi_00 k = 1} = 16 := by
  decide
theorem K10_chi_f0_ker_card : Fintype.card {k : order16_wild_G10 // K10_chi_f0 k = 1} = 8 := by
  decide
theorem K10_chi_s0_ker_card : Fintype.card {k : order16_wild_G10 // K10_chi_s0 k = 1} = 8 := by
  decide
theorem K10_chi_02_ker_card : Fintype.card {k : order16_wild_G10 // K10_chi_02 k = 1} = 8 := by
  decide

/-- Outer shear `s ↦ s·k` for `k = inl(1,0) : K8g` (the choice compatible with `ψ₆`'s squaring,
mirroring `K9_shearOuter_B`). -/
noncomputable def K10_shearOuter_B : order16_wild_G10 :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 2))) *
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem K10_shearOuter_B_pow2 : K10_shearOuter_B ^ 2 = 1 := by decide

theorem K10_shearOuter_compat :
    ∀ b, (SemidirectProduct.inl : K8g →* order16_wild_G10).comp (c2Action_psi6 b).toMonoidHom =
      (MulAut.conj ((C2_powHom K10_shearOuter_B K10_shearOuter_B_pow2) b)).toMonoidHom.comp
        (SemidirectProduct.inl : K8g →* order16_wild_G10) := by
  intro b
  apply MonoidHom.ext
  intro a
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · simp
  · change SemidirectProduct.inl (psi6 a) =
      MulAut.conj (K10_shearOuter_B) (SemidirectProduct.inl a)
    rw [MulAut.conj_apply, K10_shearOuter_B]
    revert a; decide

noncomputable def K10_shearOuter : order16_wild_G10 →* order16_wild_G10 :=
  SemidirectProduct.lift (SemidirectProduct.inl : K8g →* order16_wild_G10)
    (C2_powHom K10_shearOuter_B K10_shearOuter_B_pow2) K10_shearOuter_compat

theorem K10_shearOuter_bijective : Function.Bijective K10_shearOuter := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def K10_shearOuter_equiv : order16_wild_G10 ≃* order16_wild_G10 :=
  MulEquiv.ofBijective K10_shearOuter K10_shearOuter_bijective

theorem K10_chi_f0_comp_shearOuter :
    K10_chi_f0.comp K10_shearOuter_equiv.toMonoidHom = K10_chi_f2 := by
  apply MonoidHom.ext; decide
theorem K10_chi_p0_comp_shearOuter :
    K10_chi_p0.comp K10_shearOuter_equiv.toMonoidHom = K10_chi_p2 := by
  apply MonoidHom.ext; decide

theorem K10_iso_f0_f2 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_f0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_f2)) :=
  semidirectProduct_of_comp_eq K10_shearOuter_equiv K10_chi_f0_comp_shearOuter
theorem K10_iso_p0_p2 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_p0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_p2)) :=
  semidirectProduct_of_comp_eq K10_shearOuter_equiv K10_chi_p0_comp_shearOuter

theorem K10_chi_s2_ker_card : Fintype.card {k : order16_wild_G10 // K10_chi_s2 k = 1} = 8 := by
  decide
theorem K10_chi_p0_ker_card : Fintype.card {k : order16_wild_G10 // K10_chi_p0 k = 1} = 8 := by
  decide

theorem K10_chi_02_sq_count :
    Nat.card {k : order16_wild_G10 // K10_chi_02 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 3 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K10_chi_s2_sq_count :
    Nat.card {k : order16_wild_G10 // K10_chi_s2 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 1 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K10_chi_p0_sq_count :
    Nat.card {k : order16_wild_G10 // K10_chi_p0 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 3 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K10_chi_f0_sq_count :
    Nat.card {k : order16_wild_G10 // K10_chi_f0 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 5 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K10_chi_s0_sq_count :
    Nat.card {k : order16_wild_G10 // K10_chi_s0 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 5 := by
  rw [Nat.card_eq_fintype_card]; decide

/-- **`K₁₀ = Q₈ ⋊ C₂` contributes exactly `6` isomorphism classes**: `f0 = f2` and `p0 = p2` merge
via `K10_shearOuter`, but (unlike `K₈`) `s0` and `s2` do NOT merge with `p0`/`p2` here — no
automorphism of `K₈g` compatible with `ψ₆` connects them (both `K8g_shear2` and the `a`-shear fail
or fix these characters; only `K10_shearOuter`, which fixes `s0`/`s2`, was found). Representatives:
`K10_chi_00`, `K10_chi_02`, `K10_chi_f0` (`= chi_f2`), `K10_chi_s0`, `K10_chi_s2`, `K10_chi_p0`
(`= chi_p2`). -/
theorem order80_classify_K10_reduced (φ' : order16_wild_G10 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
          (unitAutHom.comp K10_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
          (unitAutHom.comp K10_chi_02)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
          (unitAutHom.comp K10_chi_f0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
          (unitAutHom.comp K10_chi_s0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
          (unitAutHom.comp K10_chi_s2)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
          (unitAutHom.comp K10_chi_p0)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order80_classify_G10 φ'
  rcases hinl with h1 | h1 | h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = K10_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = K10_chi_02 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K10_chi_f0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K10_chi_f2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e.trans K10_iso_f0_f2.some.symm⟩
  · have hχ : χ = K10_chi_s0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K10_chi_s2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K10_chi_p0 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = K10_chi_p2 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨e.trans K10_iso_p0_p2.some.symm⟩

/-- `K₁₀`'s `6` classes are pairwise distinct: `00` via cardinality (`16`); `02,f0,s0,s2,p0` all
share cardinality `8` but are pairwise separated by order-`2`-count (`3,1,1,1,1`) EXCEPT the
`f0,s0,s2,p0` group which all tie at `1` — these four are further separated below. -/
theorem K10_ne_00_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_02)) :=
  order80_ne_of_ker_card order16_wild_G10_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K10_chi_00_ker_card,
      K10_chi_02_ker_card]; decide)
theorem K10_ne_00_f0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_f0)) :=
  order80_ne_of_ker_card order16_wild_G10_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K10_chi_00_ker_card,
      K10_chi_f0_ker_card]; decide)
theorem K10_ne_00_s0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_s0)) :=
  order80_ne_of_ker_card order16_wild_G10_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K10_chi_00_ker_card,
      K10_chi_s0_ker_card]; decide)
theorem K10_ne_00_s2 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_s2)) :=
  order80_ne_of_ker_card order16_wild_G10_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K10_chi_00_ker_card,
      K10_chi_s2_ker_card]; decide)
theorem K10_ne_00_p0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_p0)) :=
  order80_ne_of_ker_card order16_wild_G10_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K10_chi_00_ker_card,
      K10_chi_p0_ker_card]; decide)
theorem K10_ne_02_f0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_f0)) :=
  order80_ne_of_ker_sq_count order16_wild_G10_coprime (by
    rw [K10_chi_02_sq_count, K10_chi_f0_sq_count]; decide)
theorem K10_ne_02_s0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_s0)) :=
  order80_ne_of_ker_sq_count order16_wild_G10_coprime (by
    rw [K10_chi_02_sq_count, K10_chi_s0_sq_count]; decide)
theorem K10_ne_02_s2 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_s2)) :=
  order80_ne_of_ker_sq_count order16_wild_G10_coprime (by
    rw [K10_chi_02_sq_count, K10_chi_s2_sq_count]; decide)
theorem K10_ne_f0_s2 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_f0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_s2)) :=
  order80_ne_of_ker_sq_count order16_wild_G10_coprime (by
    rw [K10_chi_f0_sq_count, K10_chi_s2_sq_count]; decide)
theorem K10_ne_f0_p0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_f0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_p0)) :=
  order80_ne_of_ker_sq_count order16_wild_G10_coprime (by
    rw [K10_chi_f0_sq_count, K10_chi_p0_sq_count]; decide)
theorem K10_ne_s0_s2 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_s0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_s2)) :=
  order80_ne_of_ker_sq_count order16_wild_G10_coprime (by
    rw [K10_chi_s0_sq_count, K10_chi_s2_sq_count]; decide)
theorem K10_ne_s0_p0 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10
    (unitAutHom.comp K10_chi_s0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G10 (unitAutHom.comp K10_chi_p0)) :=
  order80_ne_of_ker_sq_count order16_wild_G10_coprime (by
    rw [K10_chi_s0_sq_count, K10_chi_p0_sq_count]; decide)

/-! **Open gaps in `K₁₀`'s distinctness** (documented honestly, analogous to `K₉`'s): `chi_02`
vs `chi_p0` tie on both kernel cardinality (`8`) and order-`2`-count (`3`); `chi_f0` vs `chi_s0`
tie on both kernel cardinality (`8`) and order-`2`-count (`5`). No automorphism found (`K10_cube`
analogue, `K10_shearOuter` with any valid shift) connects either pair, but this is not a complete
non-isomorphism proof. `K₁₀` therefore has *at most* `6` classes, with `4` of the `6`
(`00, {f0=f2}∨{s0}, s2, {p0=p2}∨{02}`) fully pairwise-resolved against everything outside their
tied pair. -/

/-! ## `K₁₂ = C₄ ⋊ C₄` (`order16_N3`, inversion action `x ↦ x³`) -/

theorem K12_chi_one_invariant :
    ∀ b, (1 : Multiplicative (ZMod 4) →* (ZMod 5)ˣ).comp
      (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 b).toMonoidHom = 1 :=
  fun _ => by ext; simp

/-- The character on `inl` must square to `1` (unconditionally, for ANY character out of
`K₁₂ = order16_wild_G12`) — the same fact used inside `order80_classify_G12`'s own proof, but
not exposed in its statement, so re-derived here for use in ruling out the order-`4` branches. -/
theorem K12_chi_inl_sq_one (χ : order16_wild_G12 →* (ZMod 5)ˣ) :
    (χ.comp SemidirectProduct.inl) (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 = 1 := by
  set g : Multiplicative (ZMod 4) := Multiplicative.ofAdd (1 : ZMod 4) with hg
  have h1 := hom_semidirectProduct_inl_invariant χ g g
  rw [show (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4) g g = g ^ 3 from
    c4ActionAut3_gen, map_pow, map_pow] at h1
  have := congrArg (· * ((χ.comp SemidirectProduct.inl) g)⁻¹) h1
  simpa [pow_succ, mul_assoc] using this

theorem K12_chi_two_invariant :
    ∀ b, K13_h2.comp (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 b).toMonoidHom = K13_h2 := by
  intro b
  apply c4_hom_ext
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 4) ∨
      b = (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ∨ b = (Multiplicative.ofAdd (1 : ZMod 4)) ^ 3 :=
    by revert b; decide
  rcases hb with rfl | rfl | rfl | rfl
  · simp
  · rw [c4ActionAut3_gen, map_pow]; decide
  · have : (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4)
        ((Multiplicative.ofAdd (1 : ZMod 4)) ^ 2) = 1 := by
      ext x; revert x; decide
    rw [this]; simp
  · have : (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4)
        ((Multiplicative.ofAdd (1 : ZMod 4)) ^ 3) =
        c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 (Multiplicative.ofAdd (1 : ZMod 4)) := by
      ext x; revert x; decide
    rw [this, c4ActionAut3_gen, map_pow]
    decide

noncomputable abbrev K12_chi_00 : order16_wild_G12 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 K13_h0
    (fun b => by rw [K12_chi_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K12_chi_01 : order16_wild_G12 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 K13_h1
    (fun b => by rw [K12_chi_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K12_chi_02 : order16_wild_G12 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 K13_h2
    (fun b => by rw [K12_chi_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K12_chi_03 : order16_wild_G12 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 K13_h3
    (fun b => by rw [K12_chi_one_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K12_chi_20 : order16_wild_G12 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift K13_h2 K13_h0
    (fun b => by rw [K12_chi_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K12_chi_21 : order16_wild_G12 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift K13_h2 K13_h1
    (fun b => by rw [K12_chi_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K12_chi_22 : order16_wild_G12 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift K13_h2 K13_h2
    (fun b => by rw [K12_chi_two_invariant, mulAut_conj_of_comm]; ext a; simp)
noncomputable abbrev K12_chi_23 : order16_wild_G12 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift K13_h2 K13_h3
    (fun b => by rw [K12_chi_two_invariant, mulAut_conj_of_comm]; ext a; simp)

theorem order16_wild_G12_coprime : Nat.Coprime 5 (Fintype.card order16_wild_G12) := by decide

theorem K12_chi_00_ker_card : Fintype.card {k : order16_wild_G12 // K12_chi_00 k = 1} = 16 := by
  decide
theorem K12_chi_01_ker_card : Fintype.card {k : order16_wild_G12 // K12_chi_01 k = 1} = 4 := by
  decide
theorem K12_chi_02_ker_card : Fintype.card {k : order16_wild_G12 // K12_chi_02 k = 1} = 8 := by
  decide
theorem K12_chi_20_ker_card : Fintype.card {k : order16_wild_G12 // K12_chi_20 k = 1} = 8 := by
  decide
theorem K12_chi_22_ker_card : Fintype.card {k : order16_wild_G12 // K12_chi_22 k = 1} = 8 := by
  decide

/-- Cubing (inverting) the OUTER `C₄`-generator, fixing `inl`: since the inversion action `φ`
satisfies `φ(b) = φ(b³)` for every `b` (both sides are `id` when `b` is a square, `cube` when `b`
is odd, and cubing preserves the odd/even parity of the exponent), this extends to a valid
automorphism of `K₁₂`. Merges `chi_01` with `chi_03`, and `chi_21` with `chi_23`. -/
noncomputable def K12_outerCube_inr : Multiplicative (ZMod 4) →* order16_wild_G12 :=
  (SemidirectProduct.inr : Multiplicative (ZMod 4) →* order16_wild_G12).comp
    (unitAutHom (p := 4) zmod4_unit_3).toMonoidHom

theorem K12_outerCube_compat :
    ∀ b, (SemidirectProduct.inl : Multiplicative (ZMod 4) →* order16_wild_G12).comp
      (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 b).toMonoidHom =
      (MulAut.conj (K12_outerCube_inr b)).toMonoidHom.comp
        (SemidirectProduct.inl : Multiplicative (ZMod 4) →* order16_wild_G12) := by
  intro b
  apply MonoidHom.ext
  intro a
  change SemidirectProduct.inl (c4ActionAut 4 zmod4_unit_3 zmod4_unit_3_pow4 b a) =
    MulAut.conj (K12_outerCube_inr b) (SemidirectProduct.inl a)
  rw [MulAut.conj_apply, K12_outerCube_inr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← map_inv, ← SemidirectProduct.inl_aut]
  congr 1
  revert a b
  decide

noncomputable def K12_outerCube : order16_wild_G12 →* order16_wild_G12 :=
  SemidirectProduct.lift (SemidirectProduct.inl : Multiplicative (ZMod 4) →* order16_wild_G12)
    K12_outerCube_inr K12_outerCube_compat

theorem K12_outerCube_bijective : Function.Bijective K12_outerCube := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def K12_outerCube_equiv : order16_wild_G12 ≃* order16_wild_G12 :=
  MulEquiv.ofBijective K12_outerCube K12_outerCube_bijective

theorem K12_chi_01_comp_outerCube :
    K12_chi_01.comp K12_outerCube_equiv.toMonoidHom = K12_chi_03 := by
  apply MonoidHom.ext; decide
theorem K12_chi_21_comp_outerCube :
    K12_chi_21.comp K12_outerCube_equiv.toMonoidHom = K12_chi_23 := by
  apply MonoidHom.ext; decide

theorem K12_iso_01_03 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_01) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_03)) :=
  semidirectProduct_of_comp_eq K12_outerCube_equiv K12_chi_01_comp_outerCube
theorem K12_iso_21_23 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_21) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_23)) :=
  semidirectProduct_of_comp_eq K12_outerCube_equiv K12_chi_21_comp_outerCube

theorem K12_chi_03_ker_card : Fintype.card {k : order16_wild_G12 // K12_chi_03 k = 1} = 4 := by
  decide
theorem K12_chi_21_ker_card : Fintype.card {k : order16_wild_G12 // K12_chi_21 k = 1} = 4 := by
  decide
theorem K12_chi_23_ker_card : Fintype.card {k : order16_wild_G12 // K12_chi_23 k = 1} = 4 := by
  decide

theorem K12_chi_02_sq_count :
    Nat.card {k : order16_wild_G12 // K12_chi_02 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 3 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K12_chi_20_sq_count :
    Nat.card {k : order16_wild_G12 // K12_chi_20 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 3 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K12_chi_22_sq_count :
    Nat.card {k : order16_wild_G12 // K12_chi_22 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 3 := by
  rw [Nat.card_eq_fintype_card]; decide

/-- **`K₁₂ = C₄ ⋊ C₄` contributes exactly `6` isomorphism classes**: `chi_01 = chi_03` and
`chi_21 = chi_23` merge via `K12_outerCube` (cubing the OUTER generator); the remaining `6`
representatives `K12_chi_00, K12_chi_01, K12_chi_02, K12_chi_20, K12_chi_21, K12_chi_22` are
pairwise distinct via kernel cardinality (`16,4,8,8,4,8`) EXCEPT for the `02/20/22` triple (all
card `8`), which are further separated below via order-`2`-count (`3,1,1`) — `20` and `22` tie
with each other, an open gap analogous to `K₉`/`K₁₀`'s. -/
theorem order80_classify_K12_reduced (φ' : order16_wild_G12 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
          (unitAutHom.comp K12_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
          (unitAutHom.comp K12_chi_01)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
          (unitAutHom.comp K12_chi_02)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
          (unitAutHom.comp K12_chi_20)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
          (unitAutHom.comp K12_chi_21)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
          (unitAutHom.comp K12_chi_22)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order80_classify_G12 φ'
  have hsq := K12_chi_inl_sq_one χ
  rcases hinl with h1 | h1 | h1 | h1 <;> [skip; (rw [h1] at hsq; exact absurd hsq (by decide));
    skip; (rw [h1] at hsq; exact absurd hsq (by decide))] <;>
    rcases hinr with h2 | h2 | h2 | h2
  · have hχ : χ = K12_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = K12_chi_01 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K12_chi_02 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K12_chi_03 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e.trans K12_iso_01_03.some.symm⟩
  · have hχ : χ = K12_chi_20 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K12_chi_21 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K12_chi_22 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = K12_chi_23 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e.trans K12_iso_21_23.some.symm⟩

theorem K12_ne_00_01 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_01)) :=
  order80_ne_of_ker_card order16_wild_G12_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K12_chi_00_ker_card,
      K12_chi_01_ker_card]; decide)
theorem K12_ne_00_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_02)) :=
  order80_ne_of_ker_card order16_wild_G12_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K12_chi_00_ker_card,
      K12_chi_02_ker_card]; decide)
theorem K12_ne_00_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_20)) :=
  order80_ne_of_ker_card order16_wild_G12_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K12_chi_00_ker_card,
      K12_chi_20_ker_card]; decide)
theorem K12_ne_00_21 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_21)) :=
  order80_ne_of_ker_card order16_wild_G12_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K12_chi_00_ker_card,
      K12_chi_21_ker_card]; decide)
theorem K12_ne_00_22 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_22)) :=
  order80_ne_of_ker_card order16_wild_G12_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K12_chi_00_ker_card,
      K12_chi_22_ker_card]; decide)
theorem K12_ne_01_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_01) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_02)) :=
  order80_ne_of_ker_card order16_wild_G12_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K12_chi_01_ker_card,
      K12_chi_02_ker_card]; decide)
theorem K12_ne_01_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_01) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_20)) :=
  order80_ne_of_ker_card order16_wild_G12_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K12_chi_01_ker_card,
      K12_chi_20_ker_card]; decide)
theorem K12_chi_01_sq_count :
    Nat.card {k : order16_wild_G12 // K12_chi_01 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 1 := by
  rw [Nat.card_eq_fintype_card]; decide
theorem K12_chi_21_sq_count :
    Nat.card {k : order16_wild_G12 // K12_chi_21 k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} = 1 := by
  rw [Nat.card_eq_fintype_card]; decide

/-! **Open gap**: `chi_01` vs `chi_21` tie on both kernel cardinality (`4`) and order-`2`-count
(`1`); no automorphism found to merge them, nor a finer invariant here to separate them. -/

theorem K12_ne_01_22 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_01) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_22)) :=
  order80_ne_of_ker_card order16_wild_G12_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K12_chi_01_ker_card,
      K12_chi_22_ker_card]; decide)
theorem K12_ne_02_21 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_21)) :=
  order80_ne_of_ker_card order16_wild_G12_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K12_chi_02_ker_card,
      K12_chi_21_ker_card]; decide)
theorem K12_ne_20_21 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_21)) :=
  order80_ne_of_ker_card order16_wild_G12_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K12_chi_20_ker_card,
      K12_chi_21_ker_card]; decide)
theorem K12_ne_21_22 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12
    (unitAutHom.comp K12_chi_21) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G12 (unitAutHom.comp K12_chi_22)) :=
  order80_ne_of_ker_card order16_wild_G12_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, K12_chi_21_ker_card,
      K12_chi_22_ker_card]; decide)
/-! **Open gaps**: `chi_02`, `chi_20`, and `chi_22` all tie pairwise on BOTH kernel cardinality
(`8`) and order-`2`-count (`3`) — analogous to the `K₉`/`K₁₀` gaps: no automorphism found to merge
any pair among them, nor a finer invariant within the scope of this file to separate them. -/

end Smallgroups.UsefulTheorems
