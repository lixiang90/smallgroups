/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeRMExamples
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionClassifiers

namespace Smallgroups.UsefulTheorems

private def order48_G11_tauQ8Fun : QuaternionGroup 2 → QuaternionGroup 2
  | QuaternionGroup.a i =>
      (QuaternionGroup.xa (0 : ZMod 4) : QuaternionGroup 2) ^ i.val
  | QuaternionGroup.xa i =>
      (QuaternionGroup.a (1 : ZMod 4) : QuaternionGroup 2) *
        (QuaternionGroup.xa (0 : ZMod 4) : QuaternionGroup 2) ^ (i + 1).val

private theorem order48_G11_tauQ8Fun_eq (q : QuaternionGroup 2) :
    order48_G11_tauQ8Fun q = order24_tau3Q8 q := by
  rcases q with i | i <;> fin_cases i <;> decide +kernel

private def order48_G11_tau3 : MulAut order16_wild_G11 where
  toFun p := (order48_G11_tauQ8Fun p.1, p.2)
  invFun p :=
    (order48_G11_tauQ8Fun (order48_G11_tauQ8Fun p.1), p.2)
  left_inv := by
    rintro ⟨q, z⟩
    rcases q with i | i <;> fin_cases i <;> fin_cases z <;> decide
  right_inv := by
    rintro ⟨q, z⟩
    rcases q with i | i <;> fin_cases i <;> fin_cases z <;> decide
  map_mul' := by
    rintro ⟨q, z⟩ ⟨q', z'⟩
    rcases q with i | i <;> rcases q' with j | j <;>
      fin_cases i <;> fin_cases j <;> fin_cases z <;> fin_cases z' <;> decide

private theorem order48_G11_tau3_eq :
    order48_G11_tau3 = order48_RM_G11_tau3 := by
  apply MulEquiv.ext
  rintro ⟨q, z⟩
  ext
  · exact order48_G11_tauQ8Fun_eq q
  · rfl

private def order48_G11_a : order16_wild_G11 :=
  (QuaternionGroup.a (1 : ZMod 4), 1)

private def order48_G11_x : order16_wild_G11 :=
  (QuaternionGroup.xa (0 : ZMod 4), 1)

private def order48_G11_z : order16_wild_G11 :=
  (1, Multiplicative.ofAdd (1 : ZMod 2))

private def order48_G11_word {M : Type*} [Monoid M]
    (a x z : M) : order16_wild_G11 → M
  | (QuaternionGroup.a i, k) =>
      a ^ i.val * z ^ (Multiplicative.toAdd k).val
  | (QuaternionGroup.xa i, k) =>
      x * a ^ i.val * z ^ (Multiplicative.toAdd k).val

private theorem order48_G11_hom_eval {M : Type*} [Monoid M]
    (f : order16_wild_G11 →* M) (q : order16_wild_G11) :
    f q = order48_G11_word
      (f order48_G11_a) (f order48_G11_x) (f order48_G11_z) q := by
  rcases q with ⟨q, k⟩
  rcases q with i | i
  · change f (QuaternionGroup.a i, k) =
      f order48_G11_a ^ i.val * f order48_G11_z ^ (Multiplicative.toAdd k).val
    have hi : (QuaternionGroup.a i, k) =
        order48_G11_a ^ i.val *
          order48_G11_z ^ (Multiplicative.toAdd k).val := by
      revert i k
      decide
    rw [hi, map_mul, map_pow, map_pow]
  · change f (QuaternionGroup.xa i, k) =
      f order48_G11_x * f order48_G11_a ^ i.val *
        f order48_G11_z ^ (Multiplicative.toAdd k).val
    have hi : (QuaternionGroup.xa i, k) =
        order48_G11_x * order48_G11_a ^ i.val *
          order48_G11_z ^ (Multiplicative.toAdd k).val := by
      revert i k
      decide
    rw [hi, map_mul, map_mul, map_pow, map_pow]

private abbrev order48_G11_triple :=
  order16_wild_G11 × order16_wild_G11 × order16_wild_G11

private def order48_G11_e (j : ZMod 2) (i : ZMod 4) (k : ZMod 2) :
    order16_wild_G11 :=
  (if j = 0 then QuaternionGroup.a i else QuaternionGroup.xa i,
    Multiplicative.ofAdd k)

/-- Candidate order-three generator images and corresponding conjugator images,
discovered with GAP.  All uses of this table are verified by Lean's kernel. -/
private def order48_G11_conjugatorTable :
    List (order48_G11_triple × order48_G11_triple) := [
  ((order48_G11_e 1 2 0, order48_G11_e 1 3 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 0 1, order48_G11_e 1 1 1, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 0 0, order48_G11_e 1 1 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 0 1, order48_G11_e 1 3 1, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 2 1, order48_G11_e 1 3 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 0 0, order48_G11_e 1 1 1, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 0 1, order48_G11_e 1 1 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 2 0, order48_G11_e 1 3 1, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 1 0, order48_G11_e 0 1 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 1 1, order48_G11_e 1 0 0, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 3 0, order48_G11_e 0 3 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 1 1, order48_G11_e 1 2 0, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 1 1, order48_G11_e 0 1 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 3 1, order48_G11_e 1 0 1, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 3 1, order48_G11_e 0 3 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 1 1, order48_G11_e 1 0 1, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 2 0, order48_G11_e 1 1 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 2 1, order48_G11_e 1 3 1, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 0 0, order48_G11_e 1 3 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 2 1, order48_G11_e 1 1 1, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 2 1, order48_G11_e 1 1 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 2 0, order48_G11_e 1 1 1, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 0 1, order48_G11_e 1 3 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 0 0, order48_G11_e 1 3 1, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 2 0, order48_G11_e 1 3 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 0 0, order48_G11_e 1 1 0, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 0 0, order48_G11_e 1 1 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 2 0, order48_G11_e 1 1 0, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 2 1, order48_G11_e 1 3 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 2 1, order48_G11_e 1 1 0, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 0 1, order48_G11_e 1 1 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 2 1, order48_G11_e 1 1 0, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 1 0, order48_G11_e 0 3 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 1 1, order48_G11_e 1 0 0, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 3 0, order48_G11_e 0 1 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 1 1, order48_G11_e 1 2 0, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 1 1, order48_G11_e 0 3 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 3 1, order48_G11_e 1 2 1, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 3 1, order48_G11_e 0 1 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 1 1, order48_G11_e 1 2 1, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 1 0, order48_G11_e 0 1 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 3 0, order48_G11_e 1 0 0, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 3 0, order48_G11_e 0 3 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 3 0, order48_G11_e 1 2 0, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 1 1, order48_G11_e 0 1 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 3 0, order48_G11_e 1 0 1, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 3 1, order48_G11_e 0 3 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 3 0, order48_G11_e 1 2 1, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 2 0, order48_G11_e 1 1 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 2 0, order48_G11_e 1 3 0, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 0 0, order48_G11_e 1 3 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 0 0, order48_G11_e 1 3 0, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 2 1, order48_G11_e 1 1 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 2 1, order48_G11_e 1 3 0, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 0 1, order48_G11_e 1 3 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 2 1, order48_G11_e 1 3 0, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 1 0, order48_G11_e 0 3 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 1 0, order48_G11_e 1 0 0, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 3 0, order48_G11_e 0 1 0, order48_G11_e 0 0 1),
    (order48_G11_e 1 1 0, order48_G11_e 1 2 0, order48_G11_e 0 0 1)),
  ((order48_G11_e 1 1 1, order48_G11_e 0 3 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 1 0, order48_G11_e 1 2 1, order48_G11_e 0 2 1)),
  ((order48_G11_e 1 3 1, order48_G11_e 0 1 1, order48_G11_e 0 0 1),
    (order48_G11_e 1 1 0, order48_G11_e 1 0 1, order48_G11_e 0 2 1))]

private def order48_G11_conjugatorImages (a x z : order16_wild_G11) :
    order48_G11_triple :=
  match order48_G11_conjugatorTable.find? (fun p => p.1 = (a, x, z)) with
  | some p => p.2
  | none => (order48_G11_a, order48_G11_x, order48_G11_z)

private def order48_G11_decidableExistsThree {α : Type*} [Fintype α]
    (p : α → α → α → Prop) (hp : ∀ a b c, Decidable (p a b c)) :
    Decidable (∃ a b c, p a b c) :=
  @Fintype.decidableExistsFintype α (fun a => ∃ b c, p a b c)
    (fun a => @Fintype.decidableExistsFintype α (fun b => ∃ c, p a b c)
      (fun b => @Fintype.decidableExistsFintype α (p a b)
        (fun c => hp a b c) inferInstance) inferInstance) inferInstance

private def order48_G11_decidableForallThree {α : Type*} [Fintype α]
    (p : α → α → α → Prop) (hp : ∀ a b c, Decidable (p a b c)) :
    Decidable (∀ a b c, p a b c) :=
  @Fintype.decidableForallFintype α (fun a => ∀ b c, p a b c)
    (fun a => @Fintype.decidableForallFintype α (fun b => ∀ c, p a b c)
      (fun b => @Fintype.decidableForallFintype α (p a b)
        (fun c => hp a b c) inferInstance) inferInstance) inferInstance

private def order48_G11_decidableImp {p q : Prop}
    (hp : Decidable p) (hq : Decidable q) : Decidable (p → q) :=
  match hp, hq with
  | isFalse hp, _ => isTrue (fun h => False.elim (hp h))
  | isTrue _, isTrue hq => isTrue (fun _ => hq)
  | isTrue hp, isFalse hq => isFalse (fun h => hq (h hp))

private def order48_G11_conjugacyWitness
    (a x z u v w : order16_wild_G11) : Prop :=
  order48_G11_word u v w (order48_G11_word a x z order48_G11_a) =
      order48_G11_word (order48_G11_tau3 u) (order48_G11_tau3 v)
        (order48_G11_tau3 w) order48_G11_a ∧
  order48_G11_word u v w (order48_G11_word a x z order48_G11_x) =
      order48_G11_word (order48_G11_tau3 u) (order48_G11_tau3 v)
        (order48_G11_tau3 w) order48_G11_x ∧
  order48_G11_word u v w (order48_G11_word a x z order48_G11_z) =
      order48_G11_word (order48_G11_tau3 u) (order48_G11_tau3 v)
        (order48_G11_tau3 w) order48_G11_z ∧
  (∀ p q, order48_G11_word u v w p = order48_G11_word u v w q → p = q) ∧
  (∀ p q, order48_G11_word u v w (p * q) =
    order48_G11_word u v w p * order48_G11_word u v w q) ∧
  (∀ p, order48_G11_word u v w (order48_G11_word a x z p) =
    order48_G11_word (order48_G11_tau3 u) (order48_G11_tau3 v)
      (order48_G11_tau3 w) p)

private def order48_G11_coordinatesListed : Prop :=
  ∀ a x z : order16_wild_G11,
    a ^ 2 = x ^ 2 →
    x * a * x⁻¹ = a⁻¹ →
    z ^ 2 = 1 →
    z * a = a * z →
    z * x = x * z →
    order48_G11_word a x z (order48_G11_word a x z
      (order48_G11_word a x z order48_G11_a)) = order48_G11_a →
    order48_G11_word a x z (order48_G11_word a x z
      (order48_G11_word a x z order48_G11_x)) = order48_G11_x →
    order48_G11_word a x z (order48_G11_word a x z
      (order48_G11_word a x z order48_G11_z)) = order48_G11_z →
    ¬(a = order48_G11_a ∧ x = order48_G11_x ∧ z = order48_G11_z) →
    (∀ p, order48_G11_word a x z p = 1 → p = 1) →
    (order48_G11_conjugatorTable.find?
      (fun row => row.1 = (a, x, z))).isSome = true

private def order48_G11_coordinatesListed_decidable :
    Decidable order48_G11_coordinatesListed :=
  order48_G11_decidableForallThree _ (fun a x z => by
    have h1 : Decidable (a ^ 2 = x ^ 2) := inferInstance
    have h2 : Decidable (x * a * x⁻¹ = a⁻¹) := inferInstance
    have h3 : Decidable (z ^ 2 = 1) := inferInstance
    have h4 : Decidable (z * a = a * z) := inferInstance
    have h5 : Decidable (z * x = x * z) := inferInstance
    have h6 : Decidable (order48_G11_word a x z (order48_G11_word a x z
        (order48_G11_word a x z order48_G11_a)) = order48_G11_a) := inferInstance
    have h7 : Decidable (order48_G11_word a x z (order48_G11_word a x z
        (order48_G11_word a x z order48_G11_x)) = order48_G11_x) := inferInstance
    have h8 : Decidable (order48_G11_word a x z (order48_G11_word a x z
        (order48_G11_word a x z order48_G11_z)) = order48_G11_z) := inferInstance
    have h9 : Decidable
        (¬(a = order48_G11_a ∧ x = order48_G11_x ∧ z = order48_G11_z)) :=
      inferInstance
    have h10 : Decidable (∀ p, order48_G11_word a x z p = 1 → p = 1) :=
      inferInstance
    have h11 : Decidable ((order48_G11_conjugatorTable.find?
        (fun row => row.1 = (a, x, z))).isSome = true) := inferInstance
    exact order48_G11_decidableImp h1 <| order48_G11_decidableImp h2 <|
      order48_G11_decidableImp h3 <| order48_G11_decidableImp h4 <|
      order48_G11_decidableImp h5 <| order48_G11_decidableImp h6 <|
      order48_G11_decidableImp h7 <| order48_G11_decidableImp h8 <|
      order48_G11_decidableImp h9 <| order48_G11_decidableImp h10 h11)

set_option maxHeartbeats 600000 in
-- Kernel evaluation checks that the presentation constraints leave exactly the 32 table rows.
private theorem order48_G11_coordinatesListed_proof :
    order48_G11_coordinatesListed := by
  exact @of_decide_eq_true order48_G11_coordinatesListed
    order48_G11_coordinatesListed_decidable (by decide +kernel)

private def order48_G11_tableCorrect : Prop :=
  ∀ a x z : order16_wild_G11,
    (order48_G11_conjugatorTable.find?
      (fun row => row.1 = (a, x, z))).isSome = true →
    let t := order48_G11_conjugatorImages a x z
    order48_G11_conjugacyWitness a x z t.1 t.2.1 t.2.2

private def order48_G11_tableCorrect_decidable : Decidable order48_G11_tableCorrect :=
  order48_G11_decidableForallThree _ (fun a x z => by
    let t := order48_G11_conjugatorImages a x z
    have hp : Decidable ((order48_G11_conjugatorTable.find?
        (fun row => row.1 = (a, x, z))).isSome = true) := inferInstance
    have hq : Decidable
        (order48_G11_conjugacyWitness a x z t.1 t.2.1 t.2.2) := by
      dsimp [order48_G11_conjugacyWitness]
      infer_instance
    exact order48_G11_decidableImp hp hq)

set_option maxHeartbeats 800000 in
-- Kernel evaluation validates the conjugator and intertwining equations for every table row.
private theorem order48_G11_tableCorrect_proof : order48_G11_tableCorrect := by
  exact @of_decide_eq_true order48_G11_tableCorrect
    order48_G11_tableCorrect_decidable (by decide +kernel)

private theorem order48_G11_action_conjugate
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G11)
    (hφ : φ order48_c3Generator ≠ 1) :
    ∃ θ : MulAut order16_wild_G11,
      (MulAut.conj θ).toMonoidHom.comp φ = order48_RM_G11_action := by
  let α := φ order48_c3Generator
  let a := α order48_G11_a
  let x := α order48_G11_x
  let z := α order48_G11_z
  let F := order48_G11_word a x z
  have heval : ∀ q, α q = F q := order48_G11_hom_eval α.toMonoidHom
  have hsquares : a ^ 2 = x ^ 2 := by
    have h : order48_G11_a ^ 2 = order48_G11_x ^ 2 := by decide
    simpa [a, x] using congrArg α h
  have hconj : x * a * x⁻¹ = a⁻¹ := by
    have h : order48_G11_x * order48_G11_a * order48_G11_x⁻¹ =
        order48_G11_a⁻¹ := by decide
    simpa [a, x] using congrArg α h
  have hz2 : z ^ 2 = 1 := by
    have h : order48_G11_z ^ 2 = 1 := by decide
    simpa [z] using congrArg α h
  have hza : z * a = a * z := by
    have h : order48_G11_z * order48_G11_a =
        order48_G11_a * order48_G11_z := by decide
    simpa [a, z] using congrArg α h
  have hzx : z * x = x * z := by
    have h : order48_G11_z * order48_G11_x =
        order48_G11_x * order48_G11_z := by decide
    simpa [x, z] using congrArg α h
  have hcubeF : ∀ q, F (F (F q)) = q := by
    intro q
    have h := congrArg (fun β : MulAut order16_wild_G11 => β q)
      (order48_c3_action_generator_pow_three φ)
    rw [← heval (F (F q)), ← heval (F q), ← heval q]
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply,
      MulAut.one_apply] using h
  have hne : ¬(a = order48_G11_a ∧ x = order48_G11_x ∧ z = order48_G11_z) := by
    intro h
    apply hφ
    apply MulEquiv.ext
    intro q
    rw [heval]
    dsimp [F]
    rw [h.1, h.2.1, h.2.2]
    change _ = (MonoidHom.id order16_wild_G11) q
    exact (order48_G11_hom_eval (MonoidHom.id order16_wild_G11) q).symm
  have hker : ∀ q, F q = 1 → q = 1 := by
    intro q hq
    apply α.injective
    rw [heval]
    simpa only [map_one] using hq
  have hlisted := order48_G11_coordinatesListed_proof a x z
    hsquares hconj hz2 hza hzx (hcubeF order48_G11_a)
    (hcubeF order48_G11_x) (hcubeF order48_G11_z) hne hker
  let t := order48_G11_conjugatorImages a x z
  have ht := order48_G11_tableCorrect_proof a x z hlisted
  rcases ht with ⟨_, _, _, hinj, hmul, hinter⟩
  let T : order16_wild_G11 →* order16_wild_G11 :=
    { toFun := order48_G11_word t.1 t.2.1 t.2.2
      map_one' := by
        change t.1 ^ 0 * t.2.2 ^ 0 = 1
        simp
      map_mul' := hmul }
  let θ : MulAut order16_wild_G11 := MulEquiv.ofBijective T
    ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩
  refine ⟨θ, ?_⟩
  apply order48_c3_hom_ext
  apply MulEquiv.ext
  intro q
  change θ (α (θ.symm q)) = order48_RM_G11_tau3 q
  rw [← order48_G11_tau3_eq]
  obtain ⟨y, rfl⟩ := θ.surjective q
  rw [θ.symm_apply_apply]
  change T (α y) = order48_G11_tau3 (T y)
  change order48_G11_word t.1 t.2.1 t.2.2 (α y) =
    order48_G11_tau3 (order48_G11_word t.1 t.2.1 t.2.2 y)
  rw [heval, hinter y]
  rcases y with ⟨q, k⟩
  rcases q with i | i <;>
    simp only [order48_G11_word, map_mul, map_pow, t]

/-- Every compatible action on `G₁₁ = Q₈ × C₂` yields the
`C₂ × SL(2,3)` residual representative. -/
theorem order48_G11_action_complete : Order48WildKernelActionComplete 11 := by
  change ∀ φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G11,
    Nat.card {q : SemidirectProduct order16_wild_G11
      (Multiplicative (ZMod 3)) φ // q ^ 3 = 1} = 9 → _
  intro φ hRoots
  have hSyl := (order48_c3_action_card_sylow_three_eq_four_iff
    card_order16_wild_G11 φ).mpr hRoots
  have hne := order48_c3_action_generator_ne_one_of_card_sylow_four
    card_order16_wild_G11 φ hSyl
  obtain ⟨θ, hθ⟩ := order48_G11_action_conjugate φ hne
  exact order48_RM_G11_mem_residual_of_conj φ θ hθ

end Smallgroups.UsefulTheorems
