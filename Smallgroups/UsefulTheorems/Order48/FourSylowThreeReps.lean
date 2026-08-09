/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThree
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

/-! ### The noncentral `V₄`-by-`A₄` representative -/

/-- The `A₄`-action on `V₄` obtained from `A₄ → A₄/V₄ ≃ C₃` and the standard
order-three automorphism of `V₄`.  Its image is the unique subgroup of order
three in `Aut(V₄) ≃ S₃`. -/
noncomputable def order48_four_V4A4Action :
    alternatingGroup (Fin 4) →* MulAut (ElemAbelianRep 2) :=
  (psqPrimeActionHom 2).comp order36_A4ToC3

/-- The split noncentral extension `V₄ ⋊ A₄` whose action has image of order
three. -/
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

/-! ### The currently constructed representative family -/

/-- The eight structural representatives constructed so far.  This family is
deliberately not assigned GAP numbers; one further central `C₂`-extension of
`S₄` remains to be constructed before the residual list is complete. -/
noncomputable abbrev order48_four_knownReps : Fin 8 → Type
  | 0 => order48_four_C2xS4
  | 1 => order48_four_GL23
  | 2 => order48_four_C4fiberS4
  | 3 => order48_four_C4xA4
  | 4 => order48_four_C4centralSL23
  | 5 => order48_four_V4xA4
  | 6 => order48_four_C2xSL23
  | 7 => order48_four_V4sdA4

noncomputable instance instGroupOrder48FourKnownReps (i : Fin 8) :
    Group (order48_four_knownReps i) :=
  match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
  | 3 => inferInstance
  | 4 => inferInstance
  | 5 => inferInstance
  | 6 => inferInstance
  | 7 => inferInstance

theorem card_order48_four_knownReps (i : Fin 8) :
    Nat.card (order48_four_knownReps i) = 48 := by
  fin_cases i
  · exact card_order48_four_C2xS4
  · exact card_order48_four_GL23
  · exact card_order48_four_C4fiberS4
  · exact card_order48_four_C4xA4
  · exact card_order48_four_C4centralSL23
  · exact card_order48_four_V4xA4
  · exact card_order48_four_C2xSL23
  · exact card_order48_four_V4sdA4

end Smallgroups.UsefulTheorems
