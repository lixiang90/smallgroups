/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order80.UniqueSylowFive_K0_K8to13

/-!
# Summary: the `51` groups of order `80` with a normal Sylow `5`-subgroup

Combines the Sylow-`5`-unique (equivalently: normal, since a unique Sylow subgroup is normal)
branch of the order-`80` classification into the project's three-theorem package:

* **Exhaustiveness** (`order80_normal_classification`): every group of order `80` whose Sylow
  `5`-subgroup is unique is isomorphic to `order80_normal_reps k i` for some `k : Fin 14` (the
  isomorphism type of the order-`16` complement) and some `i < order80_normal_counts k` (the
  `Aut(K)`-orbit of the acting character).
* **Distinctness** (`order80_normal_reps_pairwise`): the `51` representatives are pairwise
  non-isomorphic.  Cross-`K` pairs are separated by recovering the complement type via
  `semidirectProduct_congr_range` (the `C₅`-copy is characteristic, being a unique coprime-index
  normal subgroup) and the pairwise non-isomorphism of the `14` order-`16` groups; within-`K`
  pairs use the per-`K` `K*_ne_*` theorems of `UniqueSylowFive_K1to7.lean` /
  `UniqueSylowFive_K0_K8to13.lean`.
* **Counting** (`order80_normal_classCount`): there are exactly
  `2+5+4+5+3+3+3+4+4+4+4+3+4+3 = 51` classes.

Together with the single class with NON-normal Sylow `5` (namely `(C₂)⁴ ⋊ C₅`, the only
order-`16` group with `5 ∣ |Aut|` being `(C₂)⁴`), this accounts for all `52` groups of order
`80`.

This file also supplies the five per-`K` reduced classifications (`K₃, K₄, K₅, K₆, K₇`) that
`UniqueSylowFive_K1to7.lean` proved the merging/distinctness ingredients for but never bundled.
-/

namespace Smallgroups.UsefulTheorems

/-! ## The five missing per-`K` reduced classifications

Each follows the `order80_classify_K2_reduced` (semidirect `K`) or `order80_classify_K1_reduced`
(direct-product `K`) template: obtain the raw character disjunction from the corresponding
`order80_classify_G*`, identify the character with the named `K*_chi_*` lift, and route merged
branches through the `K*_iso_*` theorems. -/

/-- **`K₃ = M₁₆` contributes exactly `5` isomorphism classes**: `02 = 22` via `K3_tau`,
`10 = 30` and `12 = 32` via `K3_rho`. Representatives: `00, 20, 10, 02, 12`. -/
theorem order80_classify_K3_reduced (φ' : order16_wild_G3 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
          (unitAutHom.comp K3_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
          (unitAutHom.comp K3_chi_20)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
          (unitAutHom.comp K3_chi_10)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
          (unitAutHom.comp K3_chi_02)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
          (unitAutHom.comp K3_chi_12)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order80_classify_G3 φ'
  rcases hinl with h1 | h1 | h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = K3_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = K3_chi_02 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K3_chi_10 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K3_chi_12 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = K3_chi_20 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K3_chi_22 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e.trans K3_iso_02_22.some.symm⟩
  · have hχ : χ = K3_chi_30 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e.trans K3_iso_10_30.some.symm⟩
  · have hχ : χ = K3_chi_32 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨e.trans K3_iso_12_32.some.symm⟩

/-- **`K₄ = D₁₆` contributes exactly `3` isomorphism classes**: `20 = 22` via `K4_sigma`.
Representatives: `00, 20, 02`. -/
theorem order80_classify_K4_reduced (φ' : order16_wild_G4 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4
          (unitAutHom.comp K4_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4
          (unitAutHom.comp K4_chi_20)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4
          (unitAutHom.comp K4_chi_02)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order80_classify_G4 φ'
  rcases hinl with h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = K4_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = K4_chi_02 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr ⟨e⟩
  · have hχ : χ = K4_chi_20 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K4_chi_22 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e.trans K4_iso_20_22.some.symm⟩

/-- **`K₅ = Q₁₆` contributes exactly `3` isomorphism classes**: `chiQ16_c5 = chiQ16_prod_c5` via
`K5_sigma`. Representatives: `1, chiQ16_c5, chiQ16_xa_c5`. -/
theorem order80_classify_K5_reduced
    (φ' : QuaternionGroup 4 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
          (unitAutHom.comp (1 : QuaternionGroup 4 →* (ZMod 5)ˣ))) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
          (unitAutHom.comp order80_chiQ16_c5)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
          (unitAutHom.comp order80_chiQ16_xa_c5)) := by
  obtain ⟨χ, hcases, ⟨e⟩⟩ := order80_classify_G5 φ'
  rcases hcases with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨e⟩
  · exact Or.inr <| Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr ⟨e⟩
  · exact Or.inr <| Or.inl ⟨e.trans K5_iso_c5_prod_c5.some.symm⟩

/-- **`K₆ = C₁₆` contributes exactly `3` isomorphism classes**: `chi_1 = chi_3` via
`K6_mulThree`. Representatives: `chi_0 (trivial), chi_1, chi_2`. -/
theorem order80_classify_K6_reduced
    (φ' : Multiplicative (ZMod 16) →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16))
          (unitAutHom.comp K6_chi_0)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16))
          (unitAutHom.comp K6_chi_1)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16)) φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16))
          (unitAutHom.comp K6_chi_2)) := by
  obtain ⟨χ, hcases, ⟨e⟩⟩ := order80_classify_C16 φ'
  rcases hcases with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨e⟩
  · exact Or.inr <| Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr ⟨e⟩
  · exact Or.inr <| Or.inl ⟨e.trans K6_iso_1_3.some.symm⟩

/-- **`K₇ = C₄ × C₂ × C₂` contributes exactly `4` isomorphism classes**: the `16` raw candidates
collapse to `{00}`, `{10}` (`fst_two` alone), the six-element orbit `{20 = 02 = 22 = 30 = 12 =
32}`, and the eight-element orbit `{40 = 50 = 60 = 70 = 42 = 52 = 62 = 72}`. Representatives:
`00, 10, 20, 40`. -/
theorem order80_classify_K7_reduced (φ' : order16_wild_G7 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
          (unitAutHom.comp K7_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
          (unitAutHom.comp K7_chi_10)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
          (unitAutHom.comp K7_chi_20)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
          (unitAutHom.comp K7_chi_40)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order80_classify_G7 φ'
  have hχ : χ = (χ.comp (MonoidHom.inl _ _)).coprod (χ.comp (MonoidHom.inr _ _)) :=
    (MonoidHom.coprod_unique χ).symm
  rcases hinl with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rcases hinr with h2 | h2 <;>
    rw [h1, h2] at hχ <;> subst hχ
  · exact Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨e.trans K7_iso_20_02.some.symm⟩
  · exact Or.inr <| Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨e.trans K7_iso_30_12.some.symm |>.trans K7_iso_20_30.some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨e.trans K7_iso_20_22.some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨e.trans K7_iso_20_30.some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨e.trans K7_iso_30_32.some.symm |>.trans K7_iso_20_30.some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inr ⟨e⟩
  · exact Or.inr <| Or.inr <| Or.inr
      ⟨e.trans K7_iso_50_42.some.symm |>.trans K7_iso_40_50.some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inr ⟨e.trans K7_iso_40_50.some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inr
      ⟨e.trans K7_iso_50_52.some.symm |>.trans K7_iso_40_50.some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inr ⟨e.trans K7_iso_40_60.some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inr
      ⟨e.trans K7_iso_42_62.some.symm |>.trans K7_iso_50_42.some.symm |>.trans
        K7_iso_40_50.some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inr
      ⟨e.trans K7_iso_50_70.some.symm |>.trans K7_iso_40_50.some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inr
      ⟨e.trans K7_iso_52_72.some.symm |>.trans K7_iso_50_52.some.symm |>.trans
        K7_iso_40_50.some.symm⟩

/-! ## The `51` representatives, organised by complement type -/

/-- The number of isomorphism classes of `C₅ ⋊ K` for each of the `14` order-`16` complement
types `K` (indexed to match `order16_wild_reps`):
`(C₂)⁴ : 2`, `C₈×C₂ : 5`, `SD₁₆ : 4`, `M₁₆ : 5`, `D₁₆ : 3`, `Q₁₆ : 3`, `C₁₆ : 3`,
`C₄×C₂×C₂ : 4`, `D₈×C₂ : 4`, `(C₄×C₂)⋊C₂ : 4`, `Pauli : 4`, `Q₈×C₂ : 3`, `C₄⋊C₄ : 4`,
`C₄×C₄ : 3`.  Total: `51`. -/
def order80_normal_counts : Fin 14 → ℕ
  | 0 => 2
  | 1 => 5
  | 2 => 4
  | 3 => 5
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | 7 => 4
  | 8 => 4
  | 9 => 4
  | 10 => 4
  | 11 => 3
  | 12 => 4
  | 13 => 3

/-- The `14` CONCRETE order-`16` complement models (the models actually used in the
`order80_classify_G*` theorems: for the three abelian types classified abstractly via
`partitionGroup` these are the concrete products, not the abstract `order16_A*`). -/
noncomputable def order80_normal_K : Fin 14 → Type
  | 0 => order16_wild_C2pow4
  | 1 => order16_wild_G1
  | 2 => order16_wild_G2
  | 3 => order16_wild_G3
  | 4 => order16_wild_G4
  | 5 => QuaternionGroup 4
  | 6 => Multiplicative (ZMod 16)
  | 7 => order16_wild_G7
  | 8 => order16_wild_G8
  | 9 => order16_wild_G9
  | 10 => order16_wild_G10
  | 11 => order16_wild_G11
  | 12 => order16_wild_G12
  | 13 => Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

noncomputable instance order80_normal_K_group : ∀ k, Group (order80_normal_K k)
  | 0 => inferInstanceAs (Group order16_wild_C2pow4)
  | 1 => inferInstanceAs (Group order16_wild_G1)
  | 2 => inferInstanceAs (Group order16_wild_G2)
  | 3 => inferInstanceAs (Group order16_wild_G3)
  | 4 => inferInstanceAs (Group order16_wild_G4)
  | 5 => inferInstanceAs (Group (QuaternionGroup 4))
  | 6 => inferInstanceAs (Group (Multiplicative (ZMod 16)))
  | 7 => inferInstanceAs (Group order16_wild_G7)
  | 8 => inferInstanceAs (Group order16_wild_G8)
  | 9 => inferInstanceAs (Group order16_wild_G9)
  | 10 => inferInstanceAs (Group order16_wild_G10)
  | 11 => inferInstanceAs (Group order16_wild_G11)
  | 12 => inferInstanceAs (Group order16_wild_G12)
  | 13 => inferInstanceAs (Group (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))

noncomputable instance order80_normal_K_fintype : ∀ k, Fintype (order80_normal_K k)
  | 0 => inferInstanceAs (Fintype order16_wild_C2pow4)
  | 1 => inferInstanceAs (Fintype order16_wild_G1)
  | 2 => inferInstanceAs (Fintype order16_wild_G2)
  | 3 => inferInstanceAs (Fintype order16_wild_G3)
  | 4 => inferInstanceAs (Fintype order16_wild_G4)
  | 5 => inferInstanceAs (Fintype (QuaternionGroup 4))
  | 6 => inferInstanceAs (Fintype (Multiplicative (ZMod 16)))
  | 7 => inferInstanceAs (Fintype order16_wild_G7)
  | 8 => inferInstanceAs (Fintype order16_wild_G8)
  | 9 => inferInstanceAs (Fintype order16_wild_G9)
  | 10 => inferInstanceAs (Fintype order16_wild_G10)
  | 11 => inferInstanceAs (Fintype order16_wild_G11)
  | 12 => inferInstanceAs (Fintype order16_wild_G12)
  | 13 => inferInstanceAs (Fintype (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))

/-- The `51` representative acting characters, ordered to match the disjuncts of the
corresponding `order80_classify_K*_reduced` theorem. (Defined by a flat double-literal match,
not by `![...]` vectors: `Matrix.cons`/`Fin.cases` lookups reduce poorly inside `isDefEq`,
while plain matcher applications reduce in one step.) -/
noncomputable def order80_normal_chi :
    (k : Fin 14) → Fin (order80_normal_counts k) → (order80_normal_K k →* (ZMod 5)ˣ)
  | 0, ⟨0, _⟩ => K0_chi_0000
  | 0, ⟨1, _⟩ => K0_chi_1000
  | 1, ⟨0, _⟩ => K1_chi_00
  | 1, ⟨1, _⟩ => K1_chi_20
  | 1, ⟨2, _⟩ => K1_chi_10
  | 1, ⟨3, _⟩ => K1_chi_02
  | 1, ⟨4, _⟩ => K1_chi_12
  | 2, ⟨0, _⟩ => K2_chi_00
  | 2, ⟨1, _⟩ => K2_chi_20
  | 2, ⟨2, _⟩ => K2_chi_02
  | 2, ⟨3, _⟩ => K2_chi_22
  | 3, ⟨0, _⟩ => K3_chi_00
  | 3, ⟨1, _⟩ => K3_chi_20
  | 3, ⟨2, _⟩ => K3_chi_10
  | 3, ⟨3, _⟩ => K3_chi_02
  | 3, ⟨4, _⟩ => K3_chi_12
  | 4, ⟨0, _⟩ => K4_chi_00
  | 4, ⟨1, _⟩ => K4_chi_20
  | 4, ⟨2, _⟩ => K4_chi_02
  | 5, ⟨0, _⟩ => 1
  | 5, ⟨1, _⟩ => order80_chiQ16_c5
  | 5, ⟨2, _⟩ => order80_chiQ16_xa_c5
  | 6, ⟨0, _⟩ => K6_chi_0
  | 6, ⟨1, _⟩ => K6_chi_1
  | 6, ⟨2, _⟩ => K6_chi_2
  | 7, ⟨0, _⟩ => K7_chi_00
  | 7, ⟨1, _⟩ => K7_chi_10
  | 7, ⟨2, _⟩ => K7_chi_20
  | 7, ⟨3, _⟩ => K7_chi_40
  | 8, ⟨0, _⟩ => K8_chi_00
  | 8, ⟨1, _⟩ => K8_chi_f0
  | 8, ⟨2, _⟩ => K8_chi_02
  | 8, ⟨3, _⟩ => K8_chi_s0
  | 9, ⟨0, _⟩ => K9_chi_00
  | 9, ⟨1, _⟩ => K9_chi_02
  | 9, ⟨2, _⟩ => K9_chi_t0
  | 9, ⟨3, _⟩ => K9_chi_40
  | 10, ⟨0, _⟩ => K10_chi_00
  | 10, ⟨1, _⟩ => K10_chi_02
  | 10, ⟨2, _⟩ => K10_chi_f0
  | 10, ⟨3, _⟩ => K10_chi_s2
  | 11, ⟨0, _⟩ => K11_chi_00
  | 11, ⟨1, _⟩ => K11_chi_10
  | 11, ⟨2, _⟩ => K11_chi_02
  | 12, ⟨0, _⟩ => K12_chi_00
  | 12, ⟨1, _⟩ => K12_chi_01
  | 12, ⟨2, _⟩ => K12_chi_02
  | 12, ⟨3, _⟩ => K12_chi_20
  | 13, ⟨0, _⟩ => K13_chi_00
  | 13, ⟨1, _⟩ => K13_chi_20
  | 13, ⟨2, _⟩ => K13_chi_10

/-- The `51` representative groups of order `80` with normal Sylow `5`-subgroup:
`C₅ ⋊[χ] K` over the `14` complement types `K` and their reduced character lists. -/
noncomputable def order80_normal_reps (k : Fin 14)
    (i : Fin (order80_normal_counts k)) : Type :=
  SemidirectProduct (Multiplicative (ZMod 5)) (order80_normal_K k)
    (unitAutHom.comp (order80_normal_chi k i))

noncomputable instance order80_normal_reps_group (k : Fin 14)
    (i : Fin (order80_normal_counts k)) : Group (order80_normal_reps k i) :=
  inferInstanceAs (Group (SemidirectProduct (Multiplicative (ZMod 5)) (order80_normal_K k)
    (unitAutHom.comp (order80_normal_chi k i))))

/-! ## Cardinalities and coprimality -/

theorem order80_normal_K_card (k : Fin 14) : Nat.card (order80_normal_K k) = 16 := by
  fin_cases k <;> (rw [Nat.card_eq_fintype_card]; decide)

theorem order80_normal_c5_card : Nat.card (Multiplicative (ZMod 5)) = 5 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem order80_normal_K_coprime (k : Fin 14) :
    Nat.Coprime (Nat.card (Multiplicative (ZMod 5))) (Nat.card (order80_normal_K k)) := by
  rw [order80_normal_c5_card, order80_normal_K_card]
  decide

/-- Each representative has order `80`. -/
theorem order80_normal_reps_card (k : Fin 14) (i : Fin (order80_normal_counts k)) :
    Nat.card (order80_normal_reps k i) = 80 := by
  unfold order80_normal_reps
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, order80_normal_c5_card,
    order80_normal_K_card]

/-! ## Distinctness across complement types

The concrete complement models are pairwise non-isomorphic (transporting
`order16_wild_pairwise_noniso` through the abstract-to-concrete isomorphisms), and by
`semidirectProduct_congr_range` an isomorphism of two representatives forces an isomorphism of
their complements — so representatives over different `K`-types are never isomorphic. -/

theorem order80_normal_K_iso_wild (k : Fin 14) :
    Nonempty (order80_normal_K k ≃* order16_wild_reps k) := by
  fin_cases k
  · exact ⟨order16_A5_iso_concrete.some.symm⟩
  · exact ⟨MulEquiv.refl _⟩
  · exact ⟨MulEquiv.refl _⟩
  · exact ⟨MulEquiv.refl _⟩
  · exact ⟨MulEquiv.refl _⟩
  · exact ⟨MulEquiv.refl _⟩
  · exact ⟨order16_A1_iso_concrete.some.symm⟩
  · exact ⟨MulEquiv.refl _⟩
  · exact ⟨MulEquiv.refl _⟩
  · exact ⟨MulEquiv.refl _⟩
  · exact ⟨MulEquiv.refl _⟩
  · exact ⟨MulEquiv.refl _⟩
  · exact ⟨MulEquiv.refl _⟩
  · exact ⟨order16_A3_iso_concrete.some.symm⟩

theorem order80_normal_K_pairwise : PairwiseNonMulEquiv order80_normal_K := by
  intro i j h
  obtain ⟨e⟩ := h
  obtain ⟨ei⟩ := order80_normal_K_iso_wild i
  obtain ⟨ej⟩ := order80_normal_K_iso_wild j
  exact order16_wild_pairwise_noniso i j ⟨ei.symm.trans (e.trans ej)⟩

theorem order80_normal_reps_cross_disjoint :
    ∀ k₁ k₂ : Fin 14, k₁ ≠ k₂ → ∀ (i : Fin (order80_normal_counts k₁))
      (j : Fin (order80_normal_counts k₂)),
      ¬ Nonempty (order80_normal_reps k₁ i ≃* order80_normal_reps k₂ j) := by
  intro k₁ k₂ hne i j ⟨e⟩
  exact hne (order80_normal_K_pairwise k₁ k₂
    (semidirectProduct_congr_range (order80_normal_K_coprime k₂) e))

/-! ## Distinctness within each complement type -/

set_option maxHeartbeats 1600000 in
-- `195` goals, each requiring a definitional-unfolding check of an order-`80`
-- semidirect-product type against the matching `K*_ne_*` theorem
theorem order80_normal_reps_pairwise_within :
    ∀ k, PairwiseNonMulEquiv (order80_normal_reps k) := by
  intro k
  fin_cases k
  · -- K₀ = (C₂)⁴
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K0_ne_0000_1000),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K0_ne_0000_1000)),
      rfl]
  · -- K₁ = C₈ × C₂
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K1_ne_00_20),
      absurd h (not_nonempty_iff.mpr K1_ne_00_10),
      absurd h (not_nonempty_iff.mpr K1_ne_00_02),
      absurd h (not_nonempty_iff.mpr K1_ne_00_12),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K1_ne_00_20)),
      rfl,
      absurd h (not_nonempty_iff.mpr K1_ne_20_10),
      absurd h (not_nonempty_iff.mpr K1_ne_20_02),
      absurd h (not_nonempty_iff.mpr K1_ne_20_12),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K1_ne_00_10)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K1_ne_20_10)),
      rfl,
      absurd h (not_nonempty_iff.mpr K1_ne_10_02),
      absurd h (not_nonempty_iff.mpr K1_ne_10_12),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K1_ne_00_02)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K1_ne_20_02)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K1_ne_10_02)),
      rfl,
      absurd h (not_nonempty_iff.mpr K1_ne_02_12),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K1_ne_00_12)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K1_ne_20_12)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K1_ne_10_12)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K1_ne_02_12)),
      rfl]
  · -- K₂ = SD₁₆
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K2_ne_00_20),
      absurd h (not_nonempty_iff.mpr K2_ne_00_02),
      absurd h (not_nonempty_iff.mpr K2_ne_00_22),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K2_ne_00_20)),
      rfl,
      absurd h (not_nonempty_iff.mpr K2_ne_20_02),
      absurd h (not_nonempty_iff.mpr K2_ne_20_22),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K2_ne_00_02)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K2_ne_20_02)),
      rfl,
      absurd h (not_nonempty_iff.mpr K2_ne_02_22),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K2_ne_00_22)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K2_ne_20_22)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K2_ne_02_22)),
      rfl]
  · -- K₃ = M₁₆
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K3_ne_00_20),
      absurd h (not_nonempty_iff.mpr K3_ne_00_10),
      absurd h (not_nonempty_iff.mpr K3_ne_00_02),
      absurd h (not_nonempty_iff.mpr K3_ne_00_12),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K3_ne_00_20)),
      rfl,
      absurd h (not_nonempty_iff.mpr K3_ne_20_10),
      absurd h (not_nonempty_iff.mpr K3_ne_20_02),
      absurd h (not_nonempty_iff.mpr K3_ne_20_12),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K3_ne_00_10)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K3_ne_20_10)),
      rfl,
      absurd h (not_nonempty_iff.mpr K3_ne_10_02),
      absurd h (not_nonempty_iff.mpr K3_ne_10_12),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K3_ne_00_02)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K3_ne_20_02)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K3_ne_10_02)),
      rfl,
      absurd h (not_nonempty_iff.mpr K3_ne_02_12),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K3_ne_00_12)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K3_ne_20_12)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K3_ne_10_12)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K3_ne_02_12)),
      rfl]
  · -- K₄ = D₁₆
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K4_ne_00_20),
      absurd h (not_nonempty_iff.mpr K4_ne_00_02),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K4_ne_00_20)),
      rfl,
      absurd h (not_nonempty_iff.mpr K4_ne_20_02),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K4_ne_00_02)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K4_ne_20_02)),
      rfl]
  · -- K₅ = Q₁₆
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K5_ne_1_c5),
      absurd h (not_nonempty_iff.mpr K5_ne_1_xa_c5),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K5_ne_1_c5)),
      rfl,
      absurd h (not_nonempty_iff.mpr K5_ne_c5_xa_c5),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K5_ne_1_xa_c5)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K5_ne_c5_xa_c5)),
      rfl]
  · -- K₆ = C₁₆
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K6_ne_0_1),
      absurd h (not_nonempty_iff.mpr K6_ne_0_2),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K6_ne_0_1)),
      rfl,
      absurd h (not_nonempty_iff.mpr K6_ne_1_2),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K6_ne_0_2)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K6_ne_1_2)),
      rfl]
  · -- K₇ = C₄ × C₂ × C₂
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K7_ne_00_10),
      absurd h (not_nonempty_iff.mpr K7_ne_00_20),
      absurd h (not_nonempty_iff.mpr K7_ne_00_40),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K7_ne_00_10)),
      rfl,
      absurd h (not_nonempty_iff.mpr K7_ne_10_20),
      absurd h (not_nonempty_iff.mpr K7_ne_10_40),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K7_ne_00_20)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K7_ne_10_20)),
      rfl,
      absurd h (not_nonempty_iff.mpr K7_ne_20_40),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K7_ne_00_40)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K7_ne_10_40)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K7_ne_20_40)),
      rfl]
  · -- K₈ = D₈ × C₂
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K8_ne_00_f0),
      absurd h (not_nonempty_iff.mpr K8_ne_00_02),
      absurd h (not_nonempty_iff.mpr K8_ne_00_s0),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K8_ne_00_f0)),
      rfl,
      absurd h (not_nonempty_iff.mpr K8_ne_f0_02),
      absurd h (not_nonempty_iff.mpr K8_ne_f0_s0),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K8_ne_00_02)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K8_ne_f0_02)),
      rfl,
      absurd h (not_nonempty_iff.mpr K8_ne_02_s0),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K8_ne_00_s0)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K8_ne_f0_s0)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K8_ne_02_s0)),
      rfl]
  · -- K₉ = (C₄ × C₂) ⋊[ψ₅] C₂
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K9_ne_00_02),
      absurd h (not_nonempty_iff.mpr K9_ne_00_t0),
      absurd h (not_nonempty_iff.mpr K9_ne_00_40),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K9_ne_00_02)),
      rfl,
      absurd h (not_nonempty_iff.mpr K9_ne_02_t0),
      absurd h (not_nonempty_iff.mpr K9_ne_02_40),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K9_ne_00_t0)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K9_ne_02_t0)),
      rfl,
      absurd h (not_nonempty_iff.mpr K9_ne_t0_40),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K9_ne_00_40)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K9_ne_02_40)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K9_ne_t0_40)),
      rfl]
  · -- K₁₀ = Pauli group C₄ ∘ D₈
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K10_ne_00_02),
      absurd h (not_nonempty_iff.mpr K10_ne_00_f0),
      absurd h (not_nonempty_iff.mpr K10_ne_00_s2),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K10_ne_00_02)),
      rfl,
      absurd h (not_nonempty_iff.mpr K10_ne_02_f0),
      absurd h (not_nonempty_iff.mpr K10_ne_02_s2),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K10_ne_00_f0)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K10_ne_02_f0)),
      rfl,
      absurd h (not_nonempty_iff.mpr K10_ne_f0_s2),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K10_ne_00_s2)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K10_ne_02_s2)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K10_ne_f0_s2)),
      rfl]
  · -- K₁₁ = Q₈ × C₂
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K11_ne_00_10),
      absurd h (not_nonempty_iff.mpr K11_ne_00_02),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K11_ne_00_10)),
      rfl,
      absurd h (not_nonempty_iff.mpr K11_ne_10_02),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K11_ne_00_02)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K11_ne_10_02)),
      rfl]
  · -- K₁₂ = C₄ ⋊ C₄
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K12_ne_00_01),
      absurd h (not_nonempty_iff.mpr K12_ne_00_02),
      absurd h (not_nonempty_iff.mpr K12_ne_00_20),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K12_ne_00_01)),
      rfl,
      absurd h (not_nonempty_iff.mpr K12_ne_01_02),
      absurd h (not_nonempty_iff.mpr K12_ne_01_20),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K12_ne_00_02)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K12_ne_01_02)),
      rfl,
      absurd h (not_nonempty_iff.mpr K12_ne_02_20),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K12_ne_00_20)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K12_ne_01_20)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K12_ne_02_20)),
      rfl]
  · -- K₁₃ = C₄ × C₄
    intro i j h
    fin_cases i <;> fin_cases j
    exacts [rfl,
      absurd h (not_nonempty_iff.mpr K13_ne_00_20),
      absurd h (not_nonempty_iff.mpr K13_ne_00_10),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K13_ne_00_20)),
      rfl,
      absurd h (not_nonempty_iff.mpr K13_ne_20_10),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K13_ne_00_10)),
      absurd h (not_nonempty_iff.mpr (isEmpty_mulEquiv_symm K13_ne_20_10)),
      rfl]

/-! ## The three summary theorems -/

/-- **Distinctness**: the `51` representatives are pairwise non-isomorphic. -/
theorem order80_normal_reps_pairwise :
    PairwiseNonMulEquiv (fun s : Σ k : Fin 14, Fin (order80_normal_counts k) =>
      order80_normal_reps s.1 s.2) :=
  PairwiseNonMulEquiv.sigma order80_normal_reps_pairwise_within
    order80_normal_reps_cross_disjoint

set_option maxHeartbeats 1600000 in
-- each of the `51` branches unifies an order-`80` semidirect-product type against the
-- corresponding entry of the `order80_normal_reps` family by definitional unfolding
/-- **Exhaustiveness**: every group of order `80` with a unique (equivalently, normal) Sylow
`5`-subgroup is isomorphic to one of the `51` representatives. -/
theorem order80_normal_classification {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 80) (hSyl : Nat.card (Sylow 5 G) = 1) :
    ∃ (k : Fin 14) (i : Fin (order80_normal_counts k)),
      Nonempty (G ≃* order80_normal_reps k i) := by
  rcases order80_classification_of_sylow_five_normal hG hSyl with
    ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩ |
    ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩ | ⟨χ, ⟨e⟩⟩
  · rcases order80_classify_K0_reduced (unitAutHom.comp χ) with h2 | h2
    · exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K1_reduced (unitAutHom.comp χ) with h2 | h2 | h2 | h2 | h2
    · exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨1, by decide⟩, ⟨3, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨1, by decide⟩, ⟨4, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K2_reduced (unitAutHom.comp χ) with h2 | h2 | h2 | h2
    · exact ⟨⟨2, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨2, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨2, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K3_reduced (unitAutHom.comp χ) with h2 | h2 | h2 | h2 | h2
    · exact ⟨⟨3, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨3, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨3, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨3, by decide⟩, ⟨3, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨3, by decide⟩, ⟨4, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K4_reduced (unitAutHom.comp χ) with h2 | h2 | h2
    · exact ⟨⟨4, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨4, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨4, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K5_reduced (unitAutHom.comp χ) with h2 | h2 | h2
    · exact ⟨⟨5, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨5, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨5, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K6_reduced (unitAutHom.comp χ) with h2 | h2 | h2
    · exact ⟨⟨6, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨6, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨6, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K7_reduced (unitAutHom.comp χ) with h2 | h2 | h2 | h2
    · exact ⟨⟨7, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨7, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨7, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨7, by decide⟩, ⟨3, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K8_reduced (unitAutHom.comp χ) with h2 | h2 | h2 | h2
    · exact ⟨⟨8, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨8, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨8, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨8, by decide⟩, ⟨3, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K9_reduced (unitAutHom.comp χ) with h2 | h2 | h2 | h2
    · exact ⟨⟨9, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨9, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨9, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨9, by decide⟩, ⟨3, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K10_reduced (unitAutHom.comp χ) with h2 | h2 | h2 | h2
    · exact ⟨⟨10, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨10, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨10, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨10, by decide⟩, ⟨3, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K11_reduced (unitAutHom.comp χ) with h2 | h2 | h2
    · exact ⟨⟨11, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨11, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨11, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K12_reduced (unitAutHom.comp χ) with h2 | h2 | h2 | h2
    · exact ⟨⟨12, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨12, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨12, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨12, by decide⟩, ⟨3, by decide⟩, ⟨e.trans h2.some⟩⟩
  · rcases order80_classify_K13_reduced (unitAutHom.comp χ) with h2 | h2 | h2
    · exact ⟨⟨13, by decide⟩, ⟨0, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨13, by decide⟩, ⟨1, by decide⟩, ⟨e.trans h2.some⟩⟩
    · exact ⟨⟨13, by decide⟩, ⟨2, by decide⟩, ⟨e.trans h2.some⟩⟩

/-- **Counting**: there are exactly `51` isomorphism classes of groups of order `80` with
normal Sylow `5`-subgroup. -/
theorem order80_normal_classCount :
    Nat.card (Σ k : Fin 14, Fin (order80_normal_counts k)) = 51 := by
  rw [Nat.card_eq_fintype_card]
  decide

end Smallgroups.UsefulTheorems
