/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.UniqueSylowThree_Abel
import Smallgroups.UsefulTheorems.Order48.UniqueSylowThree_K2to5
import Smallgroups.UsefulTheorems.Order48.UniqueSylowThree_K8to12

/-!
# Summary of the order-48 groups with a unique Sylow-3 subgroup

The per-complement files classify the actions of each of the fourteen groups
of order `16` on `C₃`.  This file packages their `42` reduced action orbits in
one dependent family and proves:

* every representative has order `48`;
* representatives with different order-`16` complements are non-isomorphic;
* every group of order `48` with a unique Sylow-`3` subgroup is isomorphic to
  one of the `42` representatives.

Distinctness between representatives with the same complement is supplied by
`DistinctnessNormal.lean`; no GAP numbering is used here.
-/

namespace Smallgroups.UsefulTheorems

/-- The number of reduced `C₃`-actions for each order-`16` complement, indexed
as in `order16_wild_reps`. -/
def order48_normal_counts : Fin 14 → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 2
  | 7 => 3
  | 8 => 4
  | 9 => 3
  | 10 => 4
  | 11 => 3
  | 12 => 3
  | 13 => 2

/-- Concrete models for the fourteen order-`16` complements. -/
noncomputable def order48_normal_K : Fin 14 → Type
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

noncomputable instance order48_normal_K_group : ∀ k, Group (order48_normal_K k)
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

noncomputable instance order48_normal_K_fintype : ∀ k, Fintype (order48_normal_K k)
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

/-- The reduced characters, in the order in which they occur in the fourteen
per-complement classification theorems. -/
noncomputable def order48_normal_chi :
    (k : Fin 14) → Fin (order48_normal_counts k) → (order48_normal_K k →* (ZMod 3)ˣ)
  | 0, ⟨0, _⟩ => order48_K0_chi_0
  | 0, ⟨1, _⟩ => order48_K0_chi_1
  | 1, ⟨0, _⟩ => order48_K1_chi_0
  | 1, ⟨1, _⟩ => order48_K1_chi_1
  | 1, ⟨2, _⟩ => order48_K1_chi_2
  | 2, ⟨0, _⟩ => order48_K2_chi_00
  | 2, ⟨1, _⟩ => order48_K2_chi_10
  | 2, ⟨2, _⟩ => order48_K2_chi_01
  | 2, ⟨3, _⟩ => order48_K2_chi_11
  | 3, ⟨0, _⟩ => order48_K3_chi_00
  | 3, ⟨1, _⟩ => order48_K3_chi_10
  | 3, ⟨2, _⟩ => order48_K3_chi_01
  | 4, ⟨0, _⟩ => order48_K4_chi_00
  | 4, ⟨1, _⟩ => order48_K4_chi_01
  | 4, ⟨2, _⟩ => order48_K4_chi_10
  | 5, ⟨0, _⟩ => 1
  | 5, ⟨1, _⟩ => order48_chiQ16_xa
  | 5, ⟨2, _⟩ => order48_chiQ16
  | 6, ⟨0, _⟩ => order48_K6_chi_0
  | 6, ⟨1, _⟩ => order48_K6_chi_1
  | 7, ⟨0, _⟩ => order48_K7_chi_0
  | 7, ⟨1, _⟩ => order48_K7_chi_1
  | 7, ⟨2, _⟩ => order48_K7_chi_2
  | 8, ⟨0, _⟩ => order48_K8_chi_00
  | 8, ⟨1, _⟩ => order48_K8_chi_f0
  | 8, ⟨2, _⟩ => order48_K8_chi_02
  | 8, ⟨3, _⟩ => order48_K8_chi_s0
  | 9, ⟨0, _⟩ => order48_K9_chi_00
  | 9, ⟨1, _⟩ => order48_K9_chi_02
  | 9, ⟨2, _⟩ => order48_K9_chi_t0
  | 10, ⟨0, _⟩ => order48_K10_chi_00
  | 10, ⟨1, _⟩ => order48_K10_chi_02
  | 10, ⟨2, _⟩ => order48_K10_chi_f0
  | 10, ⟨3, _⟩ => order48_K10_chi_s2
  | 11, ⟨0, _⟩ => order48_K11_chi_00
  | 11, ⟨1, _⟩ => order48_K11_chi_10
  | 11, ⟨2, _⟩ => order48_K11_chi_02
  | 12, ⟨0, _⟩ => order48_K12_chi_00
  | 12, ⟨1, _⟩ => order48_K12_chi_02
  | 12, ⟨2, _⟩ => order48_K12_chi_20
  | 13, ⟨0, _⟩ => order48_K13_chi_0
  | 13, ⟨1, _⟩ => order48_K13_chi_1

/-- The `42` representatives in the unique-Sylow-`3` branch. -/
noncomputable def order48_normal_reps (k : Fin 14)
    (i : Fin (order48_normal_counts k)) : Type :=
  SemidirectProduct (Multiplicative (ZMod 3)) (order48_normal_K k)
    (order48_action (order48_normal_chi k i))

noncomputable instance order48_normal_reps_group (k : Fin 14)
    (i : Fin (order48_normal_counts k)) : Group (order48_normal_reps k i) :=
  inferInstanceAs (Group (SemidirectProduct (Multiplicative (ZMod 3))
    (order48_normal_K k) (order48_action (order48_normal_chi k i))))

theorem order48_normal_K_card (k : Fin 14) : Nat.card (order48_normal_K k) = 16 := by
  fin_cases k <;> (rw [Nat.card_eq_fintype_card]; decide)

theorem order48_normal_c3_card : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem order48_normal_K_coprime (k : Fin 14) :
    Nat.Coprime (Nat.card (Multiplicative (ZMod 3))) (Nat.card (order48_normal_K k)) := by
  rw [order48_normal_c3_card, order48_normal_K_card]
  decide

/-- Every representative in the normal branch has order `48`. -/
theorem order48_normal_reps_card (k : Fin 14) (i : Fin (order48_normal_counts k)) :
    Nat.card (order48_normal_reps k i) = 48 := by
  unfold order48_normal_reps
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, order48_normal_c3_card,
    order48_normal_K_card]

/-- Relate the concrete complement models to the canonical order-`16` list. -/
theorem order48_normal_K_iso_wild (k : Fin 14) :
    Nonempty (order48_normal_K k ≃* order16_wild_reps k) := by
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

theorem order48_normal_K_pairwise : PairwiseNonMulEquiv order48_normal_K := by
  intro i j h
  obtain ⟨e⟩ := h
  obtain ⟨ei⟩ := order48_normal_K_iso_wild i
  obtain ⟨ej⟩ := order48_normal_K_iso_wild j
  exact order16_wild_pairwise_noniso i j ⟨ei.symm.trans (e.trans ej)⟩

/-- Representatives attached to different complement types are non-isomorphic. -/
theorem order48_normal_reps_cross_disjoint :
    ∀ k₁ k₂ : Fin 14, k₁ ≠ k₂ → ∀ (i : Fin (order48_normal_counts k₁))
      (j : Fin (order48_normal_counts k₂)),
      ¬ Nonempty (order48_normal_reps k₁ i ≃* order48_normal_reps k₂ j) := by
  intro k₁ k₂ hne i j ⟨e⟩
  exact hne (order48_normal_K_pairwise k₁ k₂
    (semidirectProduct_congr_range (order48_normal_K_coprime k₂) e))

set_option maxHeartbeats 1600000 in
-- The fourteen-way `Fin` split elaborates 42 dependent representative branches.
/-- Exhaustiveness of the unique-Sylow-`3` branch. -/
theorem order48_normal_classification {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 1) :
    ∃ (k : Fin 14) (i : Fin (order48_normal_counts k)),
      Nonempty (G ≃* order48_normal_reps k i) := by
  obtain ⟨N, K, φ, _, hcardN, hcardK, ⟨e⟩⟩ :=
    order48_semidirectProduct_of_sylow_three_normal hG hSyl
  obtain ⟨eN⟩ := prime_classification (p := 3) (by norm_num) hcardN
  obtain ⟨k, ⟨eK⟩⟩ := order16_wild_classification (G := K) hcardK
  fin_cases k
  · obtain ⟨eC⟩ := order16_A5_iso_concrete
    let eKC := eK.trans eC
    let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eKC.symm.toMonoidHom)
    rcases order48_classify_K0_reduced φ' with h | h
    · exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eKC)).trans h.some⟩⟩
    · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eKC)).trans h.some⟩⟩
  · let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eK.symm.toMonoidHom)
    rcases order48_classify_K1_reduced φ' with h | h | h
    · exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
  · let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eK.symm.toMonoidHom)
    rcases order48_classify_K2_reduced φ' with h | h | h | h
    · exact ⟨⟨2, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨2, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨2, by decide⟩, ⟨2, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
  · let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eK.symm.toMonoidHom)
    rcases order48_classify_K3_reduced φ' with h | h | h
    · exact ⟨⟨3, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨3, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨3, by decide⟩, ⟨2, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
  · let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eK.symm.toMonoidHom)
    rcases order48_classify_K4_reduced φ' with h | h | h
    · exact ⟨⟨4, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨4, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨4, by decide⟩, ⟨2, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
  · let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eK.symm.toMonoidHom)
    rcases order48_classify_K5_reduced φ' with h | h | h
    · exact ⟨⟨5, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨5, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨5, by decide⟩, ⟨2, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
  · obtain ⟨eC⟩ := order16_A1_iso_concrete
    let eKC := eK.trans eC
    let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eKC.symm.toMonoidHom)
    rcases order48_classify_K6_reduced φ' with h | h
    · exact ⟨⟨6, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eKC)).trans h.some⟩⟩
    · exact ⟨⟨6, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eKC)).trans h.some⟩⟩
  · let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eK.symm.toMonoidHom)
    rcases order48_classify_K7_reduced φ' with h | h | h
    · exact ⟨⟨7, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨7, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨7, by decide⟩, ⟨2, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
  · let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eK.symm.toMonoidHom)
    rcases order48_classify_K8_reduced φ' with h | h | h | h
    · exact ⟨⟨8, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨8, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨8, by decide⟩, ⟨2, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨8, by decide⟩, ⟨3, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
  · let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eK.symm.toMonoidHom)
    rcases order48_classify_K9_reduced φ' with h | h | h
    · exact ⟨⟨9, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨9, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨9, by decide⟩, ⟨2, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
  · let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eK.symm.toMonoidHom)
    rcases order48_classify_K10_reduced φ' with h | h | h | h
    · exact ⟨⟨10, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨10, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨10, by decide⟩, ⟨2, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨10, by decide⟩, ⟨3, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
  · let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eK.symm.toMonoidHom)
    rcases order48_classify_K11_reduced φ' with h | h | h
    · exact ⟨⟨11, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨11, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨11, by decide⟩, ⟨2, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
  · let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eK.symm.toMonoidHom)
    rcases order48_classify_K12_reduced φ' with h | h | h
    · exact ⟨⟨12, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨12, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
    · exact ⟨⟨12, by decide⟩, ⟨2, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eK)).trans h.some⟩⟩
  · obtain ⟨eC⟩ := order16_A3_iso_concrete
    let eKC := eK.trans eC
    let φ' := MonoidHom.comp (MulAut.congr eN).toMonoidHom (φ.comp eKC.symm.toMonoidHom)
    rcases order48_classify_K13_reduced φ' with h | h
    · exact ⟨⟨13, by decide⟩, ⟨0, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eKC)).trans h.some⟩⟩
    · exact ⟨⟨13, by decide⟩, ⟨1, by decide⟩,
        ⟨(e.trans (SemidirectProduct.congr' eN eKC)).trans h.some⟩⟩

/-- There are `42` entries in the reduced representative family.  Together
with `order48_normal_sigma_reps_pairwise`, this is the class count for the
unique-Sylow-`3` branch. -/
theorem order48_normal_repCount :
    Nat.card (Σ k : Fin 14, Fin (order48_normal_counts k)) = 42 := by
  rw [Nat.card_eq_fintype_card]
  decide

end Smallgroups.UsefulTheorems
