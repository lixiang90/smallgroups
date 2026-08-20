/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeRMExamples
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionClassifiers

/-!
# The `G₁₀` residual action

The standard semidirect product is the central product `C₄ * SL(2,3)`.
We first exhibit it as a quotient of `C₄ × (Q₈ ⋊ C₃)`; the remaining action
orbit is then checked on the three standard generators of the Pauli kernel.
-/

namespace Smallgroups.UsefulTheorems

private abbrev order48_G10_semidirect : Type :=
  SemidirectProduct order16_wild_G10 (Multiplicative (ZMod 3))
    order48_RM_G10_action

private noncomputable def order48_G10_A : order16_wild_G10 :=
  SemidirectProduct.inl
    (Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 2)))

private noncomputable def order48_G10_B : order16_wild_G10 :=
  SemidirectProduct.inl
    ((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 2))

private noncomputable def order48_G10_H : order16_wild_G10 :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

private noncomputable def order48_G10_D : order48_G10_semidirect :=
  SemidirectProduct.inl (order48_G10_A * order48_G10_B)

private noncomputable def order48_G10_QA : order48_G10_semidirect :=
  SemidirectProduct.inl order48_G10_A

private noncomputable def order48_G10_QX : order48_G10_semidirect :=
  SemidirectProduct.inl (order48_G10_B * order48_G10_H)

private noncomputable def order48_G10_C : order48_G10_semidirect :=
  SemidirectProduct.inr order48_c3Generator

private noncomputable def order48_G10_qword : QuaternionGroup 2 → order48_G10_semidirect
  | QuaternionGroup.a i => order48_G10_QA ^ i.val
  | QuaternionGroup.xa i => order48_G10_QX * order48_G10_QA ^ i.val

private noncomputable def order48_G10_centralProductFun
    (p : CyclicRep 4 × order24_RN) : order48_G10_semidirect :=
  order48_G10_D ^ (Multiplicative.toAdd p.1).val *
    order48_G10_qword p.2.left *
    order48_G10_C ^ (Multiplicative.toAdd p.2.right).val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3200000 in
-- This checks the 96-element presentation map entirely in the Lean kernel.
private noncomputable def order48_G10_centralProductHom :
    CyclicRep 4 × order24_RN →* order48_G10_semidirect :=
  MonoidHom.mk' order48_G10_centralProductFun (by
    intro p q
    revert p q
    decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
-- Every target coordinate has a preimage among the 96 source coordinates.
private theorem order48_G10_centralProductHom_surjective :
    Function.Surjective order48_G10_centralProductHom := by
  intro y
  revert y
  decide +kernel

private noncomputable def order48_G10_RNCenter : order24_RN :=
  SemidirectProduct.inl (QuaternionGroup.a (2 : ZMod 4))

set_option maxRecDepth 10000 in
private theorem order48_G10_RN_unique_nontrivial_involution
    (y : order24_RN) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) :
    y = order48_G10_RNCenter := by
  revert y
  decide +kernel

private theorem order48_G10_SL23_negOne_map
    (eSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) ≃* order24_RN) :
    eSL (-1) = order48_G10_RNCenter := by
  apply order48_G10_RN_unique_nontrivial_involution
  · rw [← map_pow]
    norm_num
  · intro h
    have h' := eSL.injective (h.trans eSL.map_one.symm)
    exact (by decide +kernel :
      (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ≠ 1) (by simpa using h')

private noncomputable def order48_G10_fromC4SL23
    (eSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) ≃* order24_RN) :
    CyclicRep 4 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) →*
      order48_G10_semidirect :=
  order48_G10_centralProductHom.comp
    (MulEquiv.prodCongr (MulEquiv.refl _) eSL).toMonoidHom

private theorem order48_G10_fromC4SL23_surjective
    (eSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) ≃* order24_RN) :
    Function.Surjective (order48_G10_fromC4SL23 eSL) :=
  order48_G10_centralProductHom_surjective.comp
    (MulEquiv.prodCongr (MulEquiv.refl _) eSL).surjective

set_option maxRecDepth 10000 in
private theorem order48_G10_fromC4SL23_diagonal
    (eSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) ≃* order24_RN) :
    order48_G10_fromC4SL23 eSL order48_four_c4SL23Diagonal = 1 := by
  change order48_G10_centralProductHom
    (Multiplicative.ofAdd (2 : ZMod 4), eSL (-1)) = 1
  rw [show eSL (-1) = order48_G10_RNCenter from order48_G10_SL23_negOne_map eSL]
  decide +kernel

private theorem order48_G10_fromC4SL23_kernel
    (eSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) ≃* order24_RN) :
    Subgroup.zpowers order48_four_c4SL23Diagonal =
      (order48_G10_fromC4SL23 eSL).ker := by
  have hle : Subgroup.zpowers order48_four_c4SL23Diagonal ≤
      (order48_G10_fromC4SL23 eSL).ker :=
    Subgroup.zpowers_le.mpr (by
      rw [MonoidHom.mem_ker]
      exact order48_G10_fromC4SL23_diagonal eSL)
  have hsource : Nat.card
      (CyclicRep 4 × Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 96 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have htarget : Nat.card order48_G10_semidirect = 48 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hindex : (order48_G10_fromC4SL23 eSL).ker.index = 48 := by
    rw [Subgroup.index_ker,
      MonoidHom.range_eq_top_of_surjective _
        (order48_G10_fromC4SL23_surjective eSL),
      Subgroup.card_top, htarget]
  have hkernel : Nat.card (order48_G10_fromC4SL23 eSL).ker = 2 := by
    have hmul := (order48_G10_fromC4SL23 eSL).ker.card_mul_index
    rw [hsource, hindex] at hmul
    omega
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_order48_four_c4SL23Diagonal_zpowers, hkernel]

/-- The standard `G₁₀ ⋊ C₃` action gives the central product
`C₄ * SL(2,3)`. -/
noncomputable def order48_G10_standardEquivC4centralSL23 :
    order48_four_C4centralSL23 ≃* order48_G10_semidirect := by
  let eSL := Classical.choice order24_SL23_mulEquiv_RN
  exact QuotientGroup.liftEquiv
    (Subgroup.zpowers order48_four_c4SL23Diagonal)
    (order48_G10_fromC4SL23_surjective eSL)
    (order48_G10_fromC4SL23_kernel eSL)

theorem order48_RM_G10_action_mem_residualKnownReps :
    Nonempty (order48_G10_semidirect ≃*
      order48_four_residualKnownReps 4) := by
  exact ⟨order48_G10_standardEquivC4centralSL23.symm⟩

/-! ### Uniqueness of the order-three action orbit -/

private noncomputable def order48_G10_word {M : Type*} [Monoid M]
    (a b h : M) (x : order16_wild_G10) : M :=
  a ^ (Multiplicative.toAdd x.left.1).val *
    b ^ (Multiplicative.toAdd x.left.2).val *
    h ^ (Multiplicative.toAdd x.right).val

private theorem order48_G10_hom_eval {M : Type*} [Monoid M]
    (f : order16_wild_G10 →* M) (x : order16_wild_G10) :
    f x = order48_G10_word
      (f order48_G10_A) (f order48_G10_B) (f order48_G10_H) x := by
  have hx : x = order48_G10_A ^ (Multiplicative.toAdd x.left.1).val *
      order48_G10_B ^ (Multiplicative.toAdd x.left.2).val *
      order48_G10_H ^ (Multiplicative.toAdd x.right).val := by
    revert x
    decide +kernel
  change f x = f order48_G10_A ^ (Multiplicative.toAdd x.left.1).val *
    f order48_G10_B ^ (Multiplicative.toAdd x.left.2).val *
    f order48_G10_H ^ (Multiplicative.toAdd x.right).val
  calc
    f x = f (order48_G10_A ^ (Multiplicative.toAdd x.left.1).val *
        order48_G10_B ^ (Multiplicative.toAdd x.left.2).val *
        order48_G10_H ^ (Multiplicative.toAdd x.right).val) := congrArg f hx
    _ = _ := by rw [map_mul, map_mul, map_pow, map_pow, map_pow]

private abbrev order48_G10_triple :=
  order16_wild_G10 × order16_wild_G10 × order16_wild_G10

private noncomputable def order48_G10_e (i : ZMod 4) (j k : ZMod 2) :
    order16_wild_G10 :=
  order48_G10_A ^ i.val * order48_G10_B ^ j.val * order48_G10_H ^ k.val

/-- The eight order-three generator-image triples and a conjugator for each,
discovered with GAP.  The Lean kernel verifies every row below. -/
private noncomputable def order48_G10_conjugatorTable :
    List (order48_G10_triple × order48_G10_triple) := [
  ((order48_G10_e 2 1 1, order48_G10_e 1 0 1, order48_G10_e 2 1 0),
    (order48_G10_e 0 1 1, order48_G10_e 3 0 1, order48_G10_e 2 1 0)),
  ((order48_G10_e 0 1 1, order48_G10_e 3 0 1, order48_G10_e 2 1 0),
    (order48_G10_e 2 1 1, order48_G10_e 1 0 1, order48_G10_e 0 1 0)),
  ((order48_G10_e 2 1 1, order48_G10_e 1 0 1, order48_G10_e 0 1 0),
    (order48_G10_e 2 1 1, order48_G10_e 3 0 1, order48_G10_e 0 1 0)),
  ((order48_G10_e 0 1 1, order48_G10_e 3 0 1, order48_G10_e 0 1 0),
    (order48_G10_e 0 1 1, order48_G10_e 1 0 1, order48_G10_e 2 1 0)),
  ((order48_G10_e 3 1 1, order48_G10_e 2 0 1, order48_G10_e 1 0 1),
    (order48_G10_e 1 1 1, order48_G10_e 0 0 1, order48_G10_e 2 1 0)),
  ((order48_G10_e 1 1 1, order48_G10_e 0 0 1, order48_G10_e 1 0 1),
    (order48_G10_e 1 1 1, order48_G10_e 2 0 1, order48_G10_e 2 1 0)),
  ((order48_G10_e 3 1 1, order48_G10_e 2 0 1, order48_G10_e 3 0 1),
    (order48_G10_e 3 1 1, order48_G10_e 2 0 1, order48_G10_e 0 1 0)),
  ((order48_G10_e 1 1 1, order48_G10_e 0 0 1, order48_G10_e 3 0 1),
    (order48_G10_e 3 1 1, order48_G10_e 0 0 1, order48_G10_e 0 1 0))]

private noncomputable def order48_G10_conjugatorImages
    (a b h : order16_wild_G10) : order48_G10_triple :=
  match order48_G10_conjugatorTable.find? (fun p => p.1 = (a, b, h)) with
  | some p => p.2
  | none => (order48_G10_A, order48_G10_B, order48_G10_H)

private def order48_G10_decidableForallThree {α : Type*} [Fintype α]
    (p : α → α → α → Prop) (hp : ∀ a b c, Decidable (p a b c)) :
    Decidable (∀ a b c, p a b c) :=
  @Fintype.decidableForallFintype α (fun a => ∀ b c, p a b c)
    (fun a => @Fintype.decidableForallFintype α (fun b => ∀ c, p a b c)
      (fun b => @Fintype.decidableForallFintype α (p a b)
        (fun c => hp a b c) inferInstance) inferInstance) inferInstance

private def order48_G10_decidableForallTwo {α : Type*} [Fintype α]
    (p : α → α → Prop) (hp : ∀ a b, Decidable (p a b)) :
    Decidable (∀ a b, p a b) :=
  @Fintype.decidableForallFintype α (fun a => ∀ b, p a b)
    (fun a => @Fintype.decidableForallFintype α (p a)
      (fun b => hp a b) inferInstance) inferInstance

private def order48_G10_decidableForall {α : Type*} [Fintype α]
    (p : α → Prop) (hp : ∀ a, Decidable (p a)) : Decidable (∀ a, p a) :=
  @Fintype.decidableForallFintype α p hp inferInstance

private def order48_G10_decidableImp {p q : Prop}
    (hp : Decidable p) (hq : Decidable q) : Decidable (p → q) :=
  match hp, hq with
  | isFalse hp, _ => isTrue (fun h => False.elim (hp h))
  | isTrue _, isTrue hq => isTrue (fun _ => hq)
  | isTrue hp, isFalse hq => isFalse (fun h => hq (h hp))

private noncomputable def order48_G10_conjugacyWitness
    (a b h u v w : order16_wild_G10) : Prop :=
  order48_G10_word u v w (order48_G10_word a b h order48_G10_A) =
      order48_G10_word (order48_RM_G10_tau3 u) (order48_RM_G10_tau3 v)
        (order48_RM_G10_tau3 w) order48_G10_A ∧
  order48_G10_word u v w (order48_G10_word a b h order48_G10_B) =
      order48_G10_word (order48_RM_G10_tau3 u) (order48_RM_G10_tau3 v)
        (order48_RM_G10_tau3 w) order48_G10_B ∧
  order48_G10_word u v w (order48_G10_word a b h order48_G10_H) =
      order48_G10_word (order48_RM_G10_tau3 u) (order48_RM_G10_tau3 v)
        (order48_RM_G10_tau3 w) order48_G10_H ∧
  (∀ p q, order48_G10_word u v w p = order48_G10_word u v w q → p = q) ∧
  (∀ p q, order48_G10_word u v w (p * q) =
    order48_G10_word u v w p * order48_G10_word u v w q) ∧
  (∀ p, order48_G10_word u v w (order48_G10_word a b h p) =
    order48_G10_word (order48_RM_G10_tau3 u) (order48_RM_G10_tau3 v)
      (order48_RM_G10_tau3 w) p)

private noncomputable def order48_G10_coordinatesListed : Prop :=
  ∀ a b h : order16_wild_G10,
    a ^ 4 = 1 →
    b ^ 2 = 1 →
    h ^ 2 = 1 →
    a * b = b * a →
    h * a * h⁻¹ = a⁻¹ →
    h * b * h⁻¹ = a ^ 2 * b →
    order48_G10_word a b h (order48_G10_word a b h
      (order48_G10_word a b h order48_G10_A)) = order48_G10_A →
    order48_G10_word a b h (order48_G10_word a b h
      (order48_G10_word a b h order48_G10_B)) = order48_G10_B →
    order48_G10_word a b h (order48_G10_word a b h
      (order48_G10_word a b h order48_G10_H)) = order48_G10_H →
    ¬(a = order48_G10_A ∧ b = order48_G10_B ∧ h = order48_G10_H) →
    (∀ p, order48_G10_word a b h p = 1 → p = 1) →
    (order48_G10_conjugatorTable.find?
      (fun row => row.1 = (a, b, h))).isSome = true

private noncomputable def order48_G10_coordinatesListed_decidable :
    Decidable order48_G10_coordinatesListed :=
  order48_G10_decidableForallThree _ (fun a b h => by
    have h1 : Decidable (a ^ 4 = 1) := inferInstance
    have h2 : Decidable (b ^ 2 = 1) := inferInstance
    have h3 : Decidable (h ^ 2 = 1) := inferInstance
    have h4 : Decidable (a * b = b * a) := inferInstance
    have h5 : Decidable (h * a * h⁻¹ = a⁻¹) := inferInstance
    have h6 : Decidable (h * b * h⁻¹ = a ^ 2 * b) := inferInstance
    have h7 : Decidable (order48_G10_word a b h (order48_G10_word a b h
        (order48_G10_word a b h order48_G10_A)) = order48_G10_A) := inferInstance
    have h8 : Decidable (order48_G10_word a b h (order48_G10_word a b h
        (order48_G10_word a b h order48_G10_B)) = order48_G10_B) := inferInstance
    have h9 : Decidable (order48_G10_word a b h (order48_G10_word a b h
        (order48_G10_word a b h order48_G10_H)) = order48_G10_H) := inferInstance
    have h10 : Decidable
        (¬(a = order48_G10_A ∧ b = order48_G10_B ∧ h = order48_G10_H)) :=
      inferInstance
    have h11 : Decidable (∀ p, order48_G10_word a b h p = 1 → p = 1) :=
      inferInstance
    have h12 : Decidable ((order48_G10_conjugatorTable.find?
        (fun row => row.1 = (a, b, h))).isSome = true) := inferInstance
    exact order48_G10_decidableImp h1 <| order48_G10_decidableImp h2 <|
      order48_G10_decidableImp h3 <| order48_G10_decidableImp h4 <|
      order48_G10_decidableImp h5 <| order48_G10_decidableImp h6 <|
      order48_G10_decidableImp h7 <| order48_G10_decidableImp h8 <|
      order48_G10_decidableImp h9 <| order48_G10_decidableImp h10 <|
      order48_G10_decidableImp h11 h12)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Kernel evaluation proves that the presentation constraints leave exactly these eight rows.
private theorem order48_G10_coordinatesListed_proof :
    order48_G10_coordinatesListed := by
  exact @of_decide_eq_true order48_G10_coordinatesListed
    order48_G10_coordinatesListed_decidable (by decide +kernel)

private noncomputable def order48_G10_tableCorrect : Prop :=
  ∀ a b h : order16_wild_G10,
    (order48_G10_conjugatorTable.find?
      (fun row => row.1 = (a, b, h))).isSome = true →
    let t := order48_G10_conjugatorImages a b h
    order48_G10_conjugacyWitness a b h t.1 t.2.1 t.2.2

private noncomputable def order48_G10_tableCorrect_decidable :
    Decidable order48_G10_tableCorrect :=
  order48_G10_decidableForallThree _ (fun a b h => by
    let t := order48_G10_conjugatorImages a b h
    have hp : Decidable ((order48_G10_conjugatorTable.find?
        (fun row => row.1 = (a, b, h))).isSome = true) := inferInstance
    have hq : Decidable
        (order48_G10_conjugacyWitness a b h t.1 t.2.1 t.2.2) := by
      dsimp [order48_G10_conjugacyWitness]
      letI : Decidable (∀ p q : order16_wild_G10,
          order48_G10_word t.1 t.2.1 t.2.2 p =
            order48_G10_word t.1 t.2.1 t.2.2 q → p = q) :=
        order48_G10_decidableForallTwo _ (fun p q =>
          order48_G10_decidableImp inferInstance inferInstance)
      letI : Decidable (∀ p q : order16_wild_G10,
          order48_G10_word t.1 t.2.1 t.2.2 (p * q) =
            order48_G10_word t.1 t.2.1 t.2.2 p *
              order48_G10_word t.1 t.2.1 t.2.2 q) :=
        order48_G10_decidableForallTwo _ (fun _ _ => inferInstance)
      letI : Decidable (∀ p : order16_wild_G10,
          order48_G10_word t.1 t.2.1 t.2.2 (order48_G10_word a b h p) =
            order48_G10_word (order48_RM_G10_tau3 t.1)
              (order48_RM_G10_tau3 t.2.1) (order48_RM_G10_tau3 t.2.2) p) :=
        order48_G10_decidableForall _ (fun _ => inferInstance)
      infer_instance
    exact order48_G10_decidableImp hp hq)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Kernel evaluation validates all conjugator maps and intertwining equations.
private theorem order48_G10_tableCorrect_proof : order48_G10_tableCorrect := by
  exact @of_decide_eq_true order48_G10_tableCorrect
    order48_G10_tableCorrect_decidable (by decide +kernel)

private theorem order48_G10_action_conjugate
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G10)
    (hφ : φ order48_c3Generator ≠ 1) :
    ∃ θ : MulAut order16_wild_G10,
      (MulAut.conj θ).toMonoidHom.comp φ = order48_RM_G10_action := by
  let α := φ order48_c3Generator
  let a := α order48_G10_A
  let b := α order48_G10_B
  let h := α order48_G10_H
  let F := order48_G10_word a b h
  have heval : ∀ q, α q = F q := order48_G10_hom_eval α.toMonoidHom
  have ha4 : a ^ 4 = 1 := by
    have hrel : order48_G10_A ^ 4 = 1 := by decide +kernel
    simpa [a] using congrArg α hrel
  have hb2 : b ^ 2 = 1 := by
    have hrel : order48_G10_B ^ 2 = 1 := by decide +kernel
    simpa [b] using congrArg α hrel
  have hh2 : h ^ 2 = 1 := by
    have hrel : order48_G10_H ^ 2 = 1 := by decide +kernel
    simpa [h] using congrArg α hrel
  have hab : a * b = b * a := by
    have hrel : order48_G10_A * order48_G10_B =
        order48_G10_B * order48_G10_A := by decide +kernel
    simpa [a, b] using congrArg α hrel
  have hha : h * a * h⁻¹ = a⁻¹ := by
    have hrel : order48_G10_H * order48_G10_A * order48_G10_H⁻¹ =
        order48_G10_A⁻¹ := by decide +kernel
    simpa [a, h] using congrArg α hrel
  have hhb : h * b * h⁻¹ = a ^ 2 * b := by
    have hrel : order48_G10_H * order48_G10_B * order48_G10_H⁻¹ =
        order48_G10_A ^ 2 * order48_G10_B := by decide +kernel
    simpa [a, b, h] using congrArg α hrel
  have hcubeF : ∀ q, F (F (F q)) = q := by
    intro q
    have hpow := congrArg (fun β : MulAut order16_wild_G10 => β q)
      (order48_c3_action_generator_pow_three φ)
    rw [← heval (F (F q)), ← heval (F q), ← heval q]
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply,
      MulAut.one_apply] using hpow
  have hne : ¬(a = order48_G10_A ∧ b = order48_G10_B ∧ h = order48_G10_H) := by
    intro habh
    apply hφ
    apply MulEquiv.ext
    intro q
    rw [heval]
    dsimp [F]
    rw [habh.1, habh.2.1, habh.2.2]
    change _ = (MonoidHom.id order16_wild_G10) q
    exact (order48_G10_hom_eval (MonoidHom.id order16_wild_G10) q).symm
  have hker : ∀ q, F q = 1 → q = 1 := by
    intro q hq
    apply α.injective
    rw [heval]
    simpa only [map_one] using hq
  have hlisted := order48_G10_coordinatesListed_proof a b h
    ha4 hb2 hh2 hab hha hhb (hcubeF order48_G10_A)
    (hcubeF order48_G10_B) (hcubeF order48_G10_H) hne hker
  let t := order48_G10_conjugatorImages a b h
  have ht := order48_G10_tableCorrect_proof a b h hlisted
  rcases ht with ⟨_, _, _, hinj, hmul, hinter⟩
  let T : order16_wild_G10 →* order16_wild_G10 :=
    { toFun := order48_G10_word t.1 t.2.1 t.2.2
      map_one' := by
        change t.1 ^ 0 * t.2.1 ^ 0 * t.2.2 ^ 0 = 1
        simp
      map_mul' := hmul }
  let θ : MulAut order16_wild_G10 := MulEquiv.ofBijective T
    ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩
  refine ⟨θ, ?_⟩
  apply order48_c3_hom_ext
  apply MulEquiv.ext
  intro q
  change θ (α (θ.symm q)) = order48_RM_G10_tau3 q
  obtain ⟨y, rfl⟩ := θ.surjective q
  rw [θ.symm_apply_apply]
  change T (α y) = order48_RM_G10_tau3 (T y)
  change order48_G10_word t.1 t.2.1 t.2.2 (α y) =
    order48_RM_G10_tau3 (order48_G10_word t.1 t.2.1 t.2.2 y)
  rw [heval, hinter y]
  rcases y with ⟨⟨i, j⟩, k⟩
  simp only [order48_G10_word, map_mul, map_pow, t]

/-- Every compatible action on `G₁₀` yields the `C₄ * SL(2,3)` residual
representative. -/
theorem order48_G10_action_complete : Order48WildKernelActionComplete 10 := by
  change ∀ φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G10,
    Nat.card {q : SemidirectProduct order16_wild_G10
      (Multiplicative (ZMod 3)) φ // q ^ 3 = 1} = 9 → _
  intro φ hRoots
  have hSyl := (order48_c3_action_card_sylow_three_eq_four_iff
    card_order16_wild_G10 φ).mpr hRoots
  have hne := order48_c3_action_generator_ne_one_of_card_sylow_four
    card_order16_wild_G10 φ hSyl
  obtain ⟨θ, hθ⟩ := order48_G10_action_conjugate φ hne
  refine ⟨4, ?_⟩
  obtain ⟨eφ⟩ := order48_c3_action_conj_orbit_move θ hθ
  obtain ⟨eR⟩ := order48_RM_G10_action_mem_residualKnownReps
  exact ⟨eφ.trans eR⟩

end Smallgroups.UsefulTheorems
