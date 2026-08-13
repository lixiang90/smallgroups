/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThree
import Smallgroups.UsefulTheorems.Order48.UniqueSylowThree
import Smallgroups.UsefulTheorems.PrimeSqPrimeNonabelian
import Smallgroups.UsefulTheorems.PGroupGeneration.CentralExtension
import Smallgroups.UsefulTheorems.PGroupGeneration.Reconstruction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Explicit representatives in the four-Sylow-three branch of order 48

This file starts attaching concrete group models to the structural cases in
`FourSylowThree`.  The names are intentionally structural: alignment with the
GAP small-group numbering is deferred.
-/

namespace Smallgroups.UsefulTheorems

/-! ### Direct-product and linear representatives -/

/-- The split central `C₂`-extension of `S₄`. -/
abbrev order48_four_C2xS4 : Type := CyclicRep 2 × Equiv.Perm (Fin 4)

/-- The general linear group `GL(2, 3)`, a central `C₂`-extension of `S₄`. -/
abbrev order48_four_GL23 : Type := GL (Fin 2) (ZMod 3)

/-- The split central `C₄`-extension of `A₄`. -/
abbrev order48_four_C4xA4 : Type := CyclicRep 4 × alternatingGroup (Fin 4)

/-- The split central `V₄`-extension of `A₄`. -/
abbrev order48_four_V4xA4 : Type := ElemAbelianRep 2 × alternatingGroup (Fin 4)

/-- The product `C₂ × SL(2, 3)`.  Its central `V₄` is the product of the two
central involutions, and the corresponding quotient is `A₄`. -/
abbrev order48_four_C2xSL23 : Type :=
  CyclicRep 2 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

/-! ### A central product representative -/

/-- The diagonal central involution used to form `C₄ * SL(2,3)`. -/
def order48_four_c4SL23Diagonal :
    CyclicRep 4 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
  (Multiplicative.ofAdd (2 : ZMod 4), -1)

theorem order48_four_c4SL23Diagonal_mem_center :
    order48_four_c4SL23Diagonal ∈ Subgroup.center
      (CyclicRep 4 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨a, b⟩
  ext <;> simp [order48_four_c4SL23Diagonal, mul_comm]

noncomputable instance instNormalOrder48FourC4SL23Diagonal :
    (Subgroup.zpowers order48_four_c4SL23Diagonal).Normal :=
  normal_of_le_center
    (Subgroup.zpowers_le.mpr order48_four_c4SL23Diagonal_mem_center)

/-- The central product `C₄ * SL(2,3)`, identifying the involution of `C₄`
with the scalar central involution of `SL(2,3)`. -/
noncomputable abbrev order48_four_C4centralSL23 : Type :=
  (CyclicRep 4 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ⧸
    Subgroup.zpowers order48_four_c4SL23Diagonal

/-! ### A sign fibre-product representative -/

private theorem order48_negOne_units_pow_four : (-1 : ℤˣ) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Int.units_pow_two]

/-- Reduction of `C₄` to its order-two quotient, written with target `ℤˣ` so
that it can be compared directly with the sign of a permutation. -/
noncomputable def order48_four_C4Parity : CyclicRep 4 →* ℤˣ :=
  zmodZPowHom 4 (-1 : ℤˣ) order48_negOne_units_pow_four

@[simp] theorem order48_four_C4Parity_gen :
    order48_four_C4Parity (Multiplicative.ofAdd (1 : ZMod 4)) = -1 := by
  simpa [order48_four_C4Parity] using
    zmodZPowHom_intCast 4 (-1 : ℤˣ) order48_negOne_units_pow_four (1 : ℤ)

/-- The difference of the parity character of `C₄` and the sign character of
`S₄`. -/
noncomputable abbrev order48_four_C4S4ParityDiff :
    CyclicRep 4 × Equiv.Perm (Fin 4) →* ℤˣ :=
  (order48_four_C4Parity.comp
      (MonoidHom.fst (CyclicRep 4) (Equiv.Perm (Fin 4)))) *
    (Equiv.Perm.sign.comp
      (MonoidHom.snd (CyclicRep 4) (Equiv.Perm (Fin 4))))⁻¹

/-- The fibre product `C₄ ×_{C₂} S₄` defined by parity and permutation sign. -/
abbrev order48_four_C4fiberS4 : Type := order48_four_C4S4ParityDiff.ker

theorem order48_four_C4S4ParityDiff_range_top :
    order48_four_C4S4ParityDiff.range = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  rcases Int.units_eq_one_or x with rfl | rfl
  · exact Subgroup.one_mem _
  · rw [MonoidHom.mem_range]
    refine ⟨(Multiplicative.ofAdd (1 : ZMod 4), 1), ?_⟩
    simp [order48_four_C4S4ParityDiff]

/-! ### The determinant twist of `GL(2,3)` -/

/-- The difference between the parity character of `C₄` and the determinant
character of `GL(2,3)`. -/
noncomputable abbrev order48_four_C4GL23DetDiff :
    CyclicRep 4 × order48_four_GL23 →* (ZMod 3)ˣ :=
  (order48_signC4.comp
      (MonoidHom.fst (CyclicRep 4) order48_four_GL23)) *
    (Matrix.GeneralLinearGroup.det.comp
      (MonoidHom.snd (CyclicRep 4) order48_four_GL23))⁻¹

/-- The parity/determinant fibre product, of order `96`. -/
abbrev order48_four_C4fiberGL23 : Type := order48_four_C4GL23DetDiff.ker

theorem card_range_order48_four_C4GL23DetDiff :
    Nat.card order48_four_C4GL23DetDiff.range = 2 := by
  have htarget : Nat.card ((ZMod 3)ˣ) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hdvd : Nat.card order48_four_C4GL23DetDiff.range ∣ 2 := by
    have h := order48_four_C4GL23DetDiff.range.card_subgroup_dvd_card
    rw [htarget] at h
    exact h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with hcard | hcard
  · have hrbot : order48_four_C4GL23DetDiff.range = ⊥ :=
      Subgroup.card_eq_one.mp hcard
    have hmem : order48_four_C4GL23DetDiff
        (Multiplicative.ofAdd (1 : ZMod 4), 1) ∈
        order48_four_C4GL23DetDiff.range := ⟨_, rfl⟩
    rw [hrbot] at hmem
    have hmap := Subgroup.mem_bot.mp hmem
    have hcalc : order48_four_C4GL23DetDiff
        (Multiplicative.ofAdd (1 : ZMod 4), 1) = -1 := by
      simp [order48_four_C4GL23DetDiff]
    rw [hcalc] at hmap
    exact ((by decide : (-1 : (ZMod 3)ˣ) ≠ 1) hmap).elim
  · exact hcard

theorem card_order48_four_C4fiberGL23 :
    Nat.card order48_four_C4fiberGL23 = 96 := by
  change Nat.card order48_four_C4GL23DetDiff.ker = 96
  have hprod : Nat.card (CyclicRep 4 × order48_four_GL23) = 192 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hidx : order48_four_C4GL23DetDiff.ker.index = 2 := by
    rw [Subgroup.index_ker, card_range_order48_four_C4GL23DetDiff]
  have h := order48_four_C4GL23DetDiff.ker.card_mul_index
  rw [hidx, hprod] at h
  omega

/-- The diagonal central involution in the determinant fibre product. -/
def order48_four_C4fiberGL23Diagonal : order48_four_C4fiberGL23 :=
  ⟨(Multiplicative.ofAdd (2 : ZMod 4), -1), by
    rw [MonoidHom.mem_ker]
    simp only [MonoidHom.mul_apply, MonoidHom.coe_comp, MonoidHom.coe_fst,
      Function.comp_apply, MonoidHom.inv_apply, MonoidHom.coe_snd]
    decide +kernel⟩

theorem order48_four_C4fiberGL23Diagonal_mem_center :
    order48_four_C4fiberGL23Diagonal ∈
      Subgroup.center order48_four_C4fiberGL23 := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨⟨a, b⟩, hab⟩
  apply Subtype.ext
  ext <;> simp [order48_four_C4fiberGL23Diagonal, mul_comm]

noncomputable instance instNormalOrder48FourC4fiberGL23Diagonal :
    (Subgroup.zpowers order48_four_C4fiberGL23Diagonal).Normal :=
  normal_of_le_center
    (Subgroup.zpowers_le.mpr order48_four_C4fiberGL23Diagonal_mem_center)

/-- The determinant twist of `GL(2,3)`, obtained by quotienting the fibre
product by its diagonal central involution.  This supplies the final expected
central `C₂`-extension model over `S₄`. -/
noncomputable abbrev order48_four_GL23DetTwist : Type :=
  order48_four_C4fiberGL23 ⧸
    Subgroup.zpowers order48_four_C4fiberGL23Diagonal

/-! ### The noncentral `V₄`-by-`A₄` comparison model -/

/-- The `A₄`-action on `V₄` obtained from `A₄ → A₄/V₄ ≃ C₃` and the standard
order-three automorphism of `V₄`.  Its image is the unique subgroup of order
three in `Aut(V₄) ≃ S₃`. -/
noncomputable def order48_four_V4A4Action :
    alternatingGroup (Fin 4) →* MulAut (ElemAbelianRep 2) :=
  (psqPrimeActionHom 2).comp order36_A4ToC3

/-- The split noncentral extension `V₄ ⋊ A₄` whose action has image of order
three.  The strengthened residual reduction in `FourSylowThree` excludes this
model from the four-Sylow branch; it is retained here to make the excluded
alternative concrete. -/
noncomputable abbrev order48_four_V4sdA4 : Type :=
  SemidirectProduct (ElemAbelianRep 2) (alternatingGroup (Fin 4))
    order48_four_V4A4Action

noncomputable instance instFintypeOrder48FourV4sdA4 : Fintype order48_four_V4sdA4 :=
  Fintype.ofEquiv (ElemAbelianRep 2 × alternatingGroup (Fin 4))
    SemidirectProduct.equivProd.symm

/-! ### Cardinalities and Sylow counts -/

theorem card_order48_four_C2xS4 : Nat.card order48_four_C2xS4 = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_order48_four_GL23 : Nat.card order48_four_GL23 = 48 := by
  rw [Matrix.card_GL_field]
  decide +kernel

theorem card_order48_four_C4xA4 : Nat.card order48_four_C4xA4 = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_order48_four_V4xA4 : Nat.card order48_four_V4xA4 = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_order48_four_C2xSL23 : Nat.card order48_four_C2xSL23 = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_order24_SL23 :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_center_order24_SL23 :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_pow_two_eq_one_order24_SL23 :
    pow_eq_one_card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) 2 = 2 := by
  rw [pow_eq_one_card, Nat.card_eq_fintype_card]
  decide +kernel

theorem card_order48_four_c4SL23Diagonal_zpowers :
    Nat.card (Subgroup.zpowers order48_four_c4SL23Diagonal) = 2 := by
  rw [Nat.card_zpowers]
  apply orderOf_eq_prime
  · ext <;> decide +kernel +revert
  · intro h
    have hfst := congrArg Prod.fst h
    exact (by decide +kernel :
      (order48_four_c4SL23Diagonal).1 ≠
        (1 : CyclicRep 4 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)).1) hfst

theorem card_order48_four_C4centralSL23 :
    Nat.card order48_four_C4centralSL23 = 48 := by
  have hprod :
      Nat.card (CyclicRep 4 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 96 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.zpowers order48_four_c4SL23Diagonal)
  change Nat.card (CyclicRep 4 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) =
    Nat.card order48_four_C4centralSL23 *
      Nat.card (Subgroup.zpowers order48_four_c4SL23Diagonal) at h
  rw [hprod, card_order48_four_c4SL23Diagonal_zpowers] at h
  omega

theorem card_order48_four_C4fiberS4 : Nat.card order48_four_C4fiberS4 = 48 := by
  change Nat.card order48_four_C4S4ParityDiff.ker = 48
  have hprod : Nat.card (CyclicRep 4 × Equiv.Perm (Fin 4)) = 96 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hrange : Nat.card order48_four_C4S4ParityDiff.range = 2 := by
    rw [order48_four_C4S4ParityDiff_range_top, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hidx : order48_four_C4S4ParityDiff.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange]
  have h := order48_four_C4S4ParityDiff.ker.card_mul_index
  rw [hidx, hprod] at h
  omega

theorem card_order48_four_C4fiberGL23Diagonal_zpowers :
    Nat.card (Subgroup.zpowers order48_four_C4fiberGL23Diagonal) = 2 := by
  rw [Nat.card_zpowers]
  apply orderOf_eq_prime
  · apply Subtype.ext
    ext <;> decide +kernel +revert
  · intro h
    have hfst := congrArg (fun x : order48_four_C4fiberGL23 => x.1.1) h
    exact (by decide +kernel :
      order48_four_C4fiberGL23Diagonal.1.1 ≠
        (1 : order48_four_C4fiberGL23).1.1) hfst

theorem card_order48_four_GL23DetTwist :
    Nat.card order48_four_GL23DetTwist = 48 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.zpowers order48_four_C4fiberGL23Diagonal)
  change Nat.card order48_four_C4fiberGL23 =
    Nat.card order48_four_GL23DetTwist *
      Nat.card (Subgroup.zpowers order48_four_C4fiberGL23Diagonal) at h
  rw [card_order48_four_C4fiberGL23,
    card_order48_four_C4fiberGL23Diagonal_zpowers] at h
  omega

theorem card_order48_four_V4sdA4 : Nat.card order48_four_V4sdA4 = 48 := by
  change Nat.card (SemidirectProduct _ _ _) = 48
  rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide +kernel

/-- The defining action of the noncentral representative really has image of
order three (rather than being the trivial action). -/
theorem card_range_order48_four_V4A4Action :
    Nat.card order48_four_V4A4Action.range = 3 := by
  have hrange : order48_four_V4A4Action.range = (psqPrimeActionHom 2).range := by
    rw [order48_four_V4A4Action, MonoidHom.range_comp,
      order36_A4ToC3_range_top, ← MonoidHom.range_eq_map]
  rw [hrange]
  have hdvd : Nat.card (psqPrimeActionHom 2).range ∣ 3 := by
    simpa [CyclicRep] using Subgroup.card_range_dvd (psqPrimeActionHom 2)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with hcard | hcard
  · have hrbot : (psqPrimeActionHom 2).range = ⊥ := Subgroup.card_eq_one.mp hcard
    have hmem : psqPrimeActionHom 2 (Multiplicative.ofAdd (1 : ZMod 3)) ∈
        (psqPrimeActionHom 2).range := ⟨_, rfl⟩
    rw [hrbot] at hmem
    have hgen : psqPrimeTau 2 = 1 := by
      have hmap := Subgroup.mem_bot.mp hmem
      rw [psqPrimeActionHom_gen] at hmap
      exact hmap
    have hne : psqPrimeTau 2 ≠ 1 := by
      intro h
      have hx := DFunLike.congr_fun h
        (Multiplicative.ofAdd (1 : ZMod 2), 1)
      exact (by decide +kernel :
        psqPrimeTau 2 (Multiplicative.ofAdd (1 : ZMod 2), 1) ≠
          (1 : MulAut (ElemAbelianRep 2))
            (Multiplicative.ofAdd (1 : ZMod 2), 1)) hx
    exact (hne hgen).elim
  · exact hcard

/-! ### The currently constructed residual representative family -/

/-- The eight residual representative candidates.  This family is
deliberately not assigned GAP numbers; completeness and pairwise
nonisomorphism are proved separately. -/
noncomputable abbrev order48_four_residualKnownReps : Fin 8 → Type
  | 0 => order48_four_C2xS4
  | 1 => order48_four_GL23
  | 2 => order48_four_C4fiberS4
  | 3 => order48_four_C4xA4
  | 4 => order48_four_C4centralSL23
  | 5 => order48_four_V4xA4
  | 6 => order48_four_C2xSL23
  | 7 => order48_four_GL23DetTwist

noncomputable instance instGroupOrder48FourResidualKnownReps (i : Fin 8) :
    Group (order48_four_residualKnownReps i) :=
  match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
  | 3 => inferInstance
  | 4 => inferInstance
  | 5 => inferInstance
  | 6 => inferInstance
  | 7 => inferInstance

theorem card_order48_four_residualKnownReps (i : Fin 8) :
    Nat.card (order48_four_residualKnownReps i) = 48 := by
  fin_cases i
  · exact card_order48_four_C2xS4
  · exact card_order48_four_GL23
  · exact card_order48_four_C4fiberS4
  · exact card_order48_four_C4xA4
  · exact card_order48_four_C4centralSL23
  · exact card_order48_four_V4xA4
  · exact card_order48_four_C2xSL23
  · exact card_order48_four_GL23DetTwist

/-! ### Membership in the four-Sylow-three branch -/

private theorem order48_four_pow_eq_one_card_prod
    (H K : Type*) [Group H] [Group K] (n : ℕ) :
    pow_eq_one_card (H × K) n =
      pow_eq_one_card H n * pow_eq_one_card K n := by
  unfold pow_eq_one_card
  rw [← Nat.card_prod]
  refine Nat.card_congr ⟨fun p => (⟨p.1.1, ?_⟩, ⟨p.1.2, ?_⟩),
    fun p => ⟨(p.1.1, p.2.1), ?_⟩,
    fun p => by ext <;> rfl, fun p => by ext <;> rfl⟩
  · have h := p.2
    rw [Prod.pow_mk] at h
    exact congrArg Prod.fst h
  · have h := p.2
    rw [Prod.pow_mk] at h
    exact congrArg Prod.snd h
  · rw [Prod.pow_mk]
    exact Prod.ext p.1.2 p.2.2

private theorem order48_four_pow_three_C2 :
    pow_eq_one_card (CyclicRep 2) 3 = 1 := by
  rw [pow_eq_one_card, Nat.card_eq_fintype_card]
  decide

private theorem order48_four_pow_three_C4 :
    pow_eq_one_card (CyclicRep 4) 3 = 1 := by
  rw [pow_eq_one_card, Nat.card_eq_fintype_card]
  decide

private theorem order48_four_pow_three_V4 :
    pow_eq_one_card (ElemAbelianRep 2) 3 = 1 := by
  rw [pow_eq_one_card, Nat.card_eq_fintype_card]
  decide

private theorem order48_four_pow_three_A4 :
    pow_eq_one_card (alternatingGroup (Fin 4)) 3 = 9 := by
  rw [pow_eq_one_card, Nat.card_eq_fintype_card]
  decide +kernel

theorem order48_four_pow_three_SL23 :
    pow_eq_one_card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) 3 = 9 := by
  rw [pow_eq_one_card, Nat.card_eq_fintype_card]
  decide +kernel

/-- The concrete matrix group `SL(2,3)` is the `Q₈ ⋊ C₃` representative from
the order-`24` classification.  This identification uses the complete
order-`24` classification and its separating triple `(center, roots₂,
roots₃) = (2,2,9)`. -/
theorem order24_SL23_mulEquiv_RN :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) ≃* order24_RN) := by
  obtain ⟨i, e⟩ := order24_classification card_order24_SL23
  obtain ⟨e⟩ := e
  have hcenter : order24_center_card i = 2 := by
    rw [← card_center_order24_reps i]
    exact (card_center_eq_of_mulEquiv e).symm.trans card_center_order24_SL23
  have htwo : order24_pow_two_eq_one_card i = 2 := by
    rw [← card_pow_two_eq_one_order24_reps i]
    exact (pow_eq_one_card_eq_of_mulEquiv 2 e).symm.trans
      card_pow_two_eq_one_order24_SL23
  have hthree : order24_pow_three_eq_one_card i = 9 := by
    rw [← card_pow_three_eq_one_order24_reps i]
    exact (pow_eq_one_card_eq_of_mulEquiv 3 e).symm.trans
      order48_four_pow_three_SL23
  have hi : i = 13 := by
    fin_cases i <;> simp_all [order24_center_card,
      order24_pow_two_eq_one_card, order24_pow_three_eq_one_card]
  subst i
  simpa [order24_reps] using (⟨e⟩ : Nonempty
    (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) ≃* order24_reps 13))

private theorem order48_four_pow_three_GL23 :
    pow_eq_one_card order48_four_GL23 3 = 9 := by
  rw [pow_eq_one_card, Nat.card_eq_fintype_card]
  decide +kernel

private theorem order48_four_pow_three_C4fiberS4 :
    pow_eq_one_card order48_four_C4fiberS4 3 = 9 := by
  rw [pow_eq_one_card, Nat.card_eq_fintype_card]
  decide +kernel

private theorem order48_four_pow_three_C4xSL23 :
    pow_eq_one_card
      (CyclicRep 4 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) 3 = 9 := by
  rw [order48_four_pow_eq_one_card_prod, order48_four_pow_three_C4,
    order48_four_pow_three_SL23]

private theorem order48_four_pow_three_C4centralSL23 :
    pow_eq_one_card order48_four_C4centralSL23 3 = 9 := by
  have hz2 : orderOf order48_four_c4SL23Diagonal = 2 := by
    simpa only [Nat.card_zpowers] using
      card_order48_four_c4SL23Diagonal_zpowers
  have hquot := order48_card_pow_three_eq_one_quotient_central_order_two
    (G := CyclicRep 4 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    order48_four_c4SL23Diagonal_mem_center hz2
  change pow_eq_one_card
      (CyclicRep 4 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) 3 =
    pow_eq_one_card order48_four_C4centralSL23 3 at hquot
  rw [order48_four_pow_three_C4xSL23] at hquot
  exact hquot.symm

private theorem order48_four_pow_three_C4fiberGL23 :
    pow_eq_one_card order48_four_C4fiberGL23 3 = 9 := by
  rw [pow_eq_one_card, Nat.card_eq_fintype_card]
  decide +kernel

private theorem order48_four_pow_three_GL23DetTwist :
    pow_eq_one_card order48_four_GL23DetTwist 3 = 9 := by
  have hz2 : orderOf order48_four_C4fiberGL23Diagonal = 2 := by
    simpa only [Nat.card_zpowers] using
      card_order48_four_C4fiberGL23Diagonal_zpowers
  have hquot := order48_card_pow_three_eq_one_quotient_central_order_two
    (G := order48_four_C4fiberGL23)
    order48_four_C4fiberGL23Diagonal_mem_center hz2
  change pow_eq_one_card order48_four_C4fiberGL23 3 =
    pow_eq_one_card order48_four_GL23DetTwist 3 at hquot
  rw [order48_four_pow_three_C4fiberGL23] at hquot
  exact hquot.symm

theorem card_sylow_three_order48_four_C2xS4 :
    Nat.card (Sylow 3 order48_four_C2xS4) = 4 := by
  apply order48_card_sylow_three_eq_four_of_cube_roots card_order48_four_C2xS4
  change pow_eq_one_card order48_four_C2xS4 3 = 9
  rw [order48_four_pow_eq_one_card_prod, order48_four_pow_three_C2,
    card_pow_three_eq_one_order24_RO]

theorem card_sylow_three_order48_four_C4xA4 :
    Nat.card (Sylow 3 order48_four_C4xA4) = 4 := by
  apply order48_card_sylow_three_eq_four_of_cube_roots card_order48_four_C4xA4
  change pow_eq_one_card order48_four_C4xA4 3 = 9
  rw [order48_four_pow_eq_one_card_prod, order48_four_pow_three_C4,
    order48_four_pow_three_A4]

theorem card_sylow_three_order48_four_V4xA4 :
    Nat.card (Sylow 3 order48_four_V4xA4) = 4 := by
  apply order48_card_sylow_three_eq_four_of_cube_roots card_order48_four_V4xA4
  change pow_eq_one_card order48_four_V4xA4 3 = 9
  rw [order48_four_pow_eq_one_card_prod, order48_four_pow_three_V4,
    order48_four_pow_three_A4]

theorem card_sylow_three_order48_four_C2xSL23 :
    Nat.card (Sylow 3 order48_four_C2xSL23) = 4 := by
  apply order48_card_sylow_three_eq_four_of_cube_roots card_order48_four_C2xSL23
  change pow_eq_one_card order48_four_C2xSL23 3 = 9
  rw [order48_four_pow_eq_one_card_prod, order48_four_pow_three_C2,
    order48_four_pow_three_SL23]

theorem card_sylow_three_order48_four_GL23 :
    Nat.card (Sylow 3 order48_four_GL23) = 4 := by
  apply order48_card_sylow_three_eq_four_of_cube_roots card_order48_four_GL23
  change pow_eq_one_card order48_four_GL23 3 = 9
  exact order48_four_pow_three_GL23

theorem card_sylow_three_order48_four_C4fiberS4 :
    Nat.card (Sylow 3 order48_four_C4fiberS4) = 4 := by
  apply order48_card_sylow_three_eq_four_of_cube_roots card_order48_four_C4fiberS4
  change pow_eq_one_card order48_four_C4fiberS4 3 = 9
  exact order48_four_pow_three_C4fiberS4

theorem card_sylow_three_order48_four_C4centralSL23 :
    Nat.card (Sylow 3 order48_four_C4centralSL23) = 4 := by
  apply order48_card_sylow_three_eq_four_of_cube_roots
    card_order48_four_C4centralSL23
  change pow_eq_one_card order48_four_C4centralSL23 3 = 9
  exact order48_four_pow_three_C4centralSL23

theorem card_sylow_three_order48_four_GL23DetTwist :
    Nat.card (Sylow 3 order48_four_GL23DetTwist) = 4 := by
  apply order48_card_sylow_three_eq_four_of_cube_roots
    card_order48_four_GL23DetTwist
  change pow_eq_one_card order48_four_GL23DetTwist 3 = 9
  exact order48_four_pow_three_GL23DetTwist

/-- Every displayed residual representative really lies in the branch with
four Sylow `3`-subgroups. -/
theorem card_sylow_three_order48_four_residualKnownReps (i : Fin 8) :
    Nat.card (Sylow 3 (order48_four_residualKnownReps i)) = 4 := by
  fin_cases i
  · exact card_sylow_three_order48_four_C2xS4
  · exact card_sylow_three_order48_four_GL23
  · exact card_sylow_three_order48_four_C4fiberS4
  · exact card_sylow_three_order48_four_C4xA4
  · exact card_sylow_three_order48_four_C4centralSL23
  · exact card_sylow_three_order48_four_V4xA4
  · exact card_sylow_three_order48_four_C2xSL23
  · exact card_sylow_three_order48_four_GL23DetTwist

end Smallgroups.UsefulTheorems
