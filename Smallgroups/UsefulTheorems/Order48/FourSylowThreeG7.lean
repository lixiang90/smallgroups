/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeRMExamples
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionClassifiers

/-!
# The `G₇ = C₄ × C₂ × C₂` residual action

GAP shows that `Aut(G₇)` has one conjugacy class of elements of order three.
This file verifies that orbit calculation on the three generator images and
then reduces every compatible action to the explicit representative.
-/

namespace Smallgroups.UsefulTheorems

private instance : DecidableEq order16_wild_G7 := fun x y =>
  decidable_of_iff
    (x.1.1 = y.1.1 ∧ x.1.2 = y.1.2 ∧ x.2 = y.2) (by
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact Prod.ext (Prod.ext h1 h2) h3
      · intro h
        subst h
        exact ⟨rfl, rfl, rfl⟩)

private def order48_G7_a : order16_wild_G7 :=
  ((Multiplicative.ofAdd (1 : ZMod 4), 1), 1)

private def order48_G7_b : order16_wild_G7 :=
  ((1, Multiplicative.ofAdd (1 : ZMod 2)), 1)

private def order48_G7_c : order16_wild_G7 :=
  ((1, 1), Multiplicative.ofAdd (1 : ZMod 2))

private theorem order48_G7_hom_eval {M : Type*} [Monoid M]
    (f : order16_wild_G7 →* M) (x : order16_wild_G7) :
    f x = f order48_G7_a ^ (Multiplicative.toAdd x.1.1).val *
      f order48_G7_b ^ (Multiplicative.toAdd x.1.2).val *
      f order48_G7_c ^ (Multiplicative.toAdd x.2).val := by
  have hx : x = order48_G7_a ^ (Multiplicative.toAdd x.1.1).val *
      order48_G7_b ^ (Multiplicative.toAdd x.1.2).val *
      order48_G7_c ^ (Multiplicative.toAdd x.2).val := by
    revert x
    decide
  calc
    f x = f (order48_G7_a ^ (Multiplicative.toAdd x.1.1).val *
        order48_G7_b ^ (Multiplicative.toAdd x.1.2).val *
        order48_G7_c ^ (Multiplicative.toAdd x.2).val) := congrArg f hx
    _ = _ := by rw [map_mul, map_mul, map_pow, map_pow, map_pow]

private def order48_G7_word
    (a b c x : order16_wild_G7) : order16_wild_G7 :=
  a ^ (Multiplicative.toAdd x.1.1).val *
    b ^ (Multiplicative.toAdd x.1.2).val *
    c ^ (Multiplicative.toAdd x.2).val

private abbrev order48_G7_triple :=
  order16_wild_G7 × order16_wild_G7 × order16_wild_G7

private def order48_G7_e (i : ZMod 4) (j k : ZMod 2) : order16_wild_G7 :=
  ((Multiplicative.ofAdd i, Multiplicative.ofAdd j), Multiplicative.ofAdd k)

private def order48_G7_elements : List order16_wild_G7 := [
  order48_G7_e 0 0 0, order48_G7_e 0 0 1,
  order48_G7_e 0 1 0, order48_G7_e 0 1 1,
  order48_G7_e 1 0 0, order48_G7_e 1 0 1,
  order48_G7_e 1 1 0, order48_G7_e 1 1 1,
  order48_G7_e 2 0 0, order48_G7_e 2 0 1,
  order48_G7_e 2 1 0, order48_G7_e 2 1 1,
  order48_G7_e 3 0 0, order48_G7_e 3 0 1,
  order48_G7_e 3 1 0, order48_G7_e 3 1 1]

/-- GAP was used to discover these 32 pairs.  Lean checks below, in the kernel,
that the right-hand triple defines the required conjugator for the left-hand
order-three generator images. -/
private def order48_G7_conjugatorTable :
    List (order48_G7_triple × order48_G7_triple) := [
  ((order48_G7_e 1 1 0, order48_G7_e 2 0 1, order48_G7_e 0 1 1),
    (order48_G7_e 1 0 1, order48_G7_e 2 1 1, order48_G7_e 0 1 0)),
  ((order48_G7_e 1 0 1, order48_G7_e 0 1 1, order48_G7_e 2 1 0),
    (order48_G7_e 1 1 0, order48_G7_e 2 1 1, order48_G7_e 0 0 1)),
  ((order48_G7_e 3 1 0, order48_G7_e 2 0 1, order48_G7_e 2 1 1),
    (order48_G7_e 3 0 1, order48_G7_e 2 1 1, order48_G7_e 2 1 0)),
  ((order48_G7_e 3 0 1, order48_G7_e 2 1 1, order48_G7_e 2 1 0),
    (order48_G7_e 3 1 0, order48_G7_e 2 1 1, order48_G7_e 2 0 1)),
  ((order48_G7_e 1 1 0, order48_G7_e 0 0 1, order48_G7_e 0 1 1),
    (order48_G7_e 3 0 1, order48_G7_e 0 1 1, order48_G7_e 0 1 0)),
  ((order48_G7_e 1 0 1, order48_G7_e 0 1 1, order48_G7_e 0 1 0),
    (order48_G7_e 3 1 0, order48_G7_e 0 1 1, order48_G7_e 0 0 1)),
  ((order48_G7_e 3 1 0, order48_G7_e 0 0 1, order48_G7_e 2 1 1),
    (order48_G7_e 1 0 1, order48_G7_e 0 1 1, order48_G7_e 2 1 0)),
  ((order48_G7_e 3 0 1, order48_G7_e 2 1 1, order48_G7_e 0 1 0),
    (order48_G7_e 1 1 0, order48_G7_e 0 1 1, order48_G7_e 2 0 1)),
  ((order48_G7_e 1 0 0, order48_G7_e 0 0 1, order48_G7_e 2 1 1),
    (order48_G7_e 1 0 0, order48_G7_e 2 0 1, order48_G7_e 0 1 1)),
  ((order48_G7_e 1 0 0, order48_G7_e 2 0 1, order48_G7_e 0 1 1),
    (order48_G7_e 3 0 0, order48_G7_e 2 0 1, order48_G7_e 2 1 1)),
  ((order48_G7_e 1 1 1, order48_G7_e 2 1 1, order48_G7_e 0 1 0),
    (order48_G7_e 1 0 1, order48_G7_e 2 1 0, order48_G7_e 0 1 1)),
  ((order48_G7_e 3 1 1, order48_G7_e 2 1 1, order48_G7_e 2 1 0),
    (order48_G7_e 1 0 1, order48_G7_e 0 1 0, order48_G7_e 2 1 1)),
  ((order48_G7_e 1 0 0, order48_G7_e 0 1 1, order48_G7_e 2 1 0),
    (order48_G7_e 1 0 0, order48_G7_e 2 1 1, order48_G7_e 0 0 1)),
  ((order48_G7_e 1 0 0, order48_G7_e 2 1 1, order48_G7_e 0 1 0),
    (order48_G7_e 1 0 0, order48_G7_e 0 1 1, order48_G7_e 2 0 1)),
  ((order48_G7_e 1 1 1, order48_G7_e 0 0 1, order48_G7_e 2 1 1),
    (order48_G7_e 1 1 0, order48_G7_e 2 0 1, order48_G7_e 0 1 1)),
  ((order48_G7_e 3 1 1, order48_G7_e 2 0 1, order48_G7_e 2 1 1),
    (order48_G7_e 1 1 0, order48_G7_e 0 0 1, order48_G7_e 2 1 1)),
  ((order48_G7_e 1 0 0, order48_G7_e 0 0 1, order48_G7_e 0 1 1),
    (order48_G7_e 3 0 0, order48_G7_e 0 0 1, order48_G7_e 0 1 1)),
  ((order48_G7_e 1 0 0, order48_G7_e 2 0 1, order48_G7_e 2 1 1),
    (order48_G7_e 1 0 0, order48_G7_e 0 0 1, order48_G7_e 2 1 1)),
  ((order48_G7_e 1 1 1, order48_G7_e 0 1 1, order48_G7_e 0 1 0),
    (order48_G7_e 3 0 1, order48_G7_e 0 1 0, order48_G7_e 0 1 1)),
  ((order48_G7_e 3 1 1, order48_G7_e 0 1 1, order48_G7_e 2 1 0),
    (order48_G7_e 3 0 1, order48_G7_e 2 1 0, order48_G7_e 2 1 1)),
  ((order48_G7_e 1 0 0, order48_G7_e 0 1 1, order48_G7_e 0 1 0),
    (order48_G7_e 3 0 0, order48_G7_e 0 1 1, order48_G7_e 0 0 1)),
  ((order48_G7_e 1 0 0, order48_G7_e 2 1 1, order48_G7_e 2 1 0),
    (order48_G7_e 3 0 0, order48_G7_e 2 1 1, order48_G7_e 2 0 1)),
  ((order48_G7_e 1 1 1, order48_G7_e 0 0 1, order48_G7_e 0 1 1),
    (order48_G7_e 3 1 0, order48_G7_e 0 0 1, order48_G7_e 0 1 1)),
  ((order48_G7_e 3 1 1, order48_G7_e 2 0 1, order48_G7_e 0 1 1),
    (order48_G7_e 3 1 0, order48_G7_e 2 0 1, order48_G7_e 2 1 1)),
  ((order48_G7_e 1 1 0, order48_G7_e 0 1 1, order48_G7_e 0 1 0),
    (order48_G7_e 3 1 1, order48_G7_e 0 0 1, order48_G7_e 0 1 0)),
  ((order48_G7_e 1 1 0, order48_G7_e 2 1 1, order48_G7_e 2 1 0),
    (order48_G7_e 1 1 1, order48_G7_e 2 0 1, order48_G7_e 0 1 0)),
  ((order48_G7_e 1 0 1, order48_G7_e 0 0 1, order48_G7_e 0 1 1),
    (order48_G7_e 3 1 1, order48_G7_e 0 1 0, order48_G7_e 0 0 1)),
  ((order48_G7_e 1 0 1, order48_G7_e 2 0 1, order48_G7_e 2 1 1),
    (order48_G7_e 1 1 1, order48_G7_e 2 1 0, order48_G7_e 0 0 1)),
  ((order48_G7_e 3 1 0, order48_G7_e 2 1 1, order48_G7_e 0 1 0),
    (order48_G7_e 3 1 1, order48_G7_e 2 0 1, order48_G7_e 2 1 0)),
  ((order48_G7_e 3 1 0, order48_G7_e 0 1 1, order48_G7_e 2 1 0),
    (order48_G7_e 1 1 1, order48_G7_e 0 0 1, order48_G7_e 2 1 0)),
  ((order48_G7_e 3 0 1, order48_G7_e 2 0 1, order48_G7_e 0 1 1),
    (order48_G7_e 1 1 1, order48_G7_e 0 1 0, order48_G7_e 2 0 1)),
  ((order48_G7_e 3 0 1, order48_G7_e 0 0 1, order48_G7_e 2 1 1),
    (order48_G7_e 3 1 1, order48_G7_e 2 1 0, order48_G7_e 2 0 1))]

private def order48_G7_preimage
    (u v w y : order16_wild_G7) : order16_wild_G7 :=
  (order48_G7_elements.find? (fun x => order48_G7_word u v w x = y)).getD 1

private def order48_G7_inverseImages (t : order48_G7_triple) :
    order48_G7_triple :=
  (order48_G7_preimage t.1 t.2.1 t.2.2 order48_G7_a,
    order48_G7_preimage t.1 t.2.1 t.2.2 order48_G7_b,
    order48_G7_preimage t.1 t.2.1 t.2.2 order48_G7_c)

private def order48_G7_conjugatorImages (a b c : order16_wild_G7) :
    order48_G7_triple :=
  match order48_G7_conjugatorTable.find? (fun p => p.1 = (a, b, c)) with
  | some p => order48_G7_inverseImages p.2
  | none => (order48_G7_a, order48_G7_b, order48_G7_c)

private def order48_decidableExistsThree {α : Type*} [Fintype α]
    (p : α → α → α → Prop) (hp : ∀ a b c, Decidable (p a b c)) :
    Decidable (∃ a b c, p a b c) :=
  @Fintype.decidableExistsFintype α (fun a => ∃ b c, p a b c)
    (fun a => @Fintype.decidableExistsFintype α (fun b => ∃ c, p a b c)
      (fun b => @Fintype.decidableExistsFintype α (p a b)
        (fun c => hp a b c) inferInstance) inferInstance) inferInstance

private def order48_decidableForallThree {α : Type*} [Fintype α]
    (p : α → α → α → Prop) (hp : ∀ a b c, Decidable (p a b c)) :
    Decidable (∀ a b c, p a b c) :=
  @Fintype.decidableForallFintype α (fun a => ∀ b c, p a b c)
    (fun a => @Fintype.decidableForallFintype α (fun b => ∀ c, p a b c)
      (fun b => @Fintype.decidableForallFintype α (p a b)
        (fun c => hp a b c) inferInstance) inferInstance) inferInstance

private def order48_decidableImp {p q : Prop}
    (hp : Decidable p) (hq : Decidable q) : Decidable (p → q) :=
  match hp, hq with
  | isFalse hp, _ => isTrue (fun h => False.elim (hp h))
  | isTrue _, isTrue hq => isTrue (fun _ => hq)
  | isTrue hp, isFalse hq => isFalse (fun h => hq (h hp))

private def order48_G7_conjugacyWitness
    (a b c u v w : order16_wild_G7) : Prop :=
  order48_G7_word u v w (order48_G7_word a b c order48_G7_a) =
      order48_G7_word
        (order48_RM_G7_tau3 u) (order48_RM_G7_tau3 v)
        (order48_RM_G7_tau3 w) order48_G7_a ∧
  order48_G7_word u v w (order48_G7_word a b c order48_G7_b) =
      order48_G7_word
        (order48_RM_G7_tau3 u) (order48_RM_G7_tau3 v)
        (order48_RM_G7_tau3 w) order48_G7_b ∧
  order48_G7_word u v w (order48_G7_word a b c order48_G7_c) =
      order48_G7_word
        (order48_RM_G7_tau3 u) (order48_RM_G7_tau3 v)
        (order48_RM_G7_tau3 w) order48_G7_c ∧
  (∀ x y, order48_G7_word u v w x =
    order48_G7_word u v w y → x = y) ∧
  (∀ x y, order48_G7_word u v w (x * y) =
    order48_G7_word u v w x * order48_G7_word u v w y) ∧
  (∀ x, order48_G7_word u v w (order48_G7_word a b c x) =
    order48_G7_word
      (order48_RM_G7_tau3 u) (order48_RM_G7_tau3 v)
      (order48_RM_G7_tau3 w) x)

private def order48_G7_coordinatesListed : Prop :=
  ∀ (a b c : order16_wild_G7),
    a ^ 4 = 1 →
    b ^ 2 = 1 →
    c ^ 2 = 1 →
    order48_G7_word a b c
      (order48_G7_word a b c
        (order48_G7_word a b c order48_G7_a)) = order48_G7_a →
    order48_G7_word a b c
      (order48_G7_word a b c
        (order48_G7_word a b c order48_G7_b)) = order48_G7_b →
    order48_G7_word a b c
      (order48_G7_word a b c
        (order48_G7_word a b c order48_G7_c)) = order48_G7_c →
    ¬(a = order48_G7_a ∧ b = order48_G7_b ∧ c = order48_G7_c) →
    (∀ x, order48_G7_word a b c x = 1 → x = 1) →
    (order48_G7_conjugatorTable.find?
      (fun p => p.1 = (a, b, c))).isSome = true

private def order48_G7_coordinatesListed_decidable :
    Decidable order48_G7_coordinatesListed :=
  order48_decidableForallThree _ (fun a b c => by
    have hq : Decidable ((order48_G7_conjugatorTable.find?
        (fun p => p.1 = (a, b, c))).isSome = true) := inferInstance
    have ha4 : Decidable (a ^ 4 = 1) := inferInstance
    have hb2 : Decidable (b ^ 2 = 1) := inferInstance
    have hc2 : Decidable (c ^ 2 = 1) := inferInstance
    have hca : Decidable (order48_G7_word a b c
        (order48_G7_word a b c
          (order48_G7_word a b c order48_G7_a)) = order48_G7_a) := inferInstance
    have hcb : Decidable (order48_G7_word a b c
        (order48_G7_word a b c
          (order48_G7_word a b c order48_G7_b)) = order48_G7_b) := inferInstance
    have hcc : Decidable (order48_G7_word a b c
        (order48_G7_word a b c
          (order48_G7_word a b c order48_G7_c)) = order48_G7_c) := inferInstance
    have hk : Decidable (∀ x, order48_G7_word a b c x = 1 → x = 1) :=
      inferInstance
    have hn : Decidable
        (¬(a = order48_G7_a ∧ b = order48_G7_b ∧ c = order48_G7_c)) :=
      inferInstance
    exact order48_decidableImp ha4 <| order48_decidableImp hb2 <|
      order48_decidableImp hc2 <| order48_decidableImp hca <|
      order48_decidableImp hcb <| order48_decidableImp hcc <|
      order48_decidableImp hn <| order48_decidableImp hk hq)

private theorem order48_G7_coordinatesListed_proof :
    order48_G7_coordinatesListed := by
  exact @of_decide_eq_true order48_G7_coordinatesListed
    order48_G7_coordinatesListed_decidable (by decide +kernel)

private def order48_G7_tableCorrect : Prop :=
  ∀ a b c : order16_wild_G7,
    (order48_G7_conjugatorTable.find?
      (fun p => p.1 = (a, b, c))).isSome = true →
    let t := order48_G7_conjugatorImages a b c
    order48_G7_conjugacyWitness a b c t.1 t.2.1 t.2.2

private def order48_G7_tableCorrect_decidable :
    Decidable order48_G7_tableCorrect :=
  order48_decidableForallThree _ (fun a b c => by
    let t := order48_G7_conjugatorImages a b c
    have hp : Decidable ((order48_G7_conjugatorTable.find?
        (fun p => p.1 = (a, b, c))).isSome = true) := inferInstance
    have hq : Decidable (order48_G7_conjugacyWitness
        a b c t.1 t.2.1 t.2.2) := by
      dsimp [order48_G7_conjugacyWitness]
      infer_instance
    exact order48_decidableImp hp hq)

set_option maxHeartbeats 800000 in
-- Kernel evaluation validates the 32 explicit GAP-discovered conjugator rows.
private theorem order48_G7_tableCorrect_proof : order48_G7_tableCorrect := by
  exact @of_decide_eq_true order48_G7_tableCorrect
    order48_G7_tableCorrect_decidable (by decide +kernel)

private theorem order48_G7_order_three_coordinates
    (a b c : order16_wild_G7)
    (ha4 : a ^ 4 = 1) (hb2 : b ^ 2 = 1) (hc2 : c ^ 2 = 1)
    (hcubeA : order48_G7_word a b c
      (order48_G7_word a b c
        (order48_G7_word a b c order48_G7_a)) = order48_G7_a)
    (hcubeB : order48_G7_word a b c
      (order48_G7_word a b c
        (order48_G7_word a b c order48_G7_b)) = order48_G7_b)
    (hcubeC : order48_G7_word a b c
      (order48_G7_word a b c
        (order48_G7_word a b c order48_G7_c)) = order48_G7_c)
    (hne : ¬(a = order48_G7_a ∧ b = order48_G7_b ∧ c = order48_G7_c))
    (hinj : ∀ x y, order48_G7_word a b c x =
      order48_G7_word a b c y → x = y)
    (_hmulIn : ∀ x y, order48_G7_word a b c (x * y) =
      order48_G7_word a b c x * order48_G7_word a b c y) :
    ∃ (u v w : order16_wild_G7),
      (∀ x y, order48_G7_word u v w x =
        order48_G7_word u v w y → x = y) ∧
      (∀ x y, order48_G7_word u v w (x * y) =
        order48_G7_word u v w x * order48_G7_word u v w y) ∧
      (∀ x, order48_G7_word u v w (order48_G7_word a b c x) =
        order48_G7_word
          (order48_RM_G7_tau3 u) (order48_RM_G7_tau3 v)
          (order48_RM_G7_tau3 w) x) := by
  let t := order48_G7_conjugatorImages a b c
  have hker : ∀ y, order48_G7_word a b c y = 1 → y = 1 := by
    intro y hy
    apply hinj y 1
    simpa [order48_G7_word] using hy
  have hlisted := order48_G7_coordinatesListed_proof a b c ha4 hb2 hc2
    hcubeA hcubeB hcubeC hne hker
  have ht := order48_G7_tableCorrect_proof a b c hlisted
  rcases ht with ⟨_, _, _, hinj', hmul', hinter⟩
  exact ⟨t.1, t.2.1, t.2.2, hinj', hmul', hinter⟩

private theorem order48_G7_action_conjugate
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G7)
    (hφ : φ order48_c3Generator ≠ 1) :
    ∃ θ : MulAut order16_wild_G7,
      (MulAut.conj θ).toMonoidHom.comp φ = order48_RM_G7_action := by
  let α := φ order48_c3Generator
  let a := α order48_G7_a
  let b := α order48_G7_b
  let c := α order48_G7_c
  let F := order48_G7_word a b c
  have heval : ∀ x, α x = F x := order48_G7_hom_eval α.toMonoidHom
  have ha4 : a ^ 4 = 1 := by
    have h : order48_G7_a ^ 4 = 1 := by decide
    simpa [a] using congrArg α h
  have hb2 : b ^ 2 = 1 := by
    have h : order48_G7_b ^ 2 = 1 := by decide
    simpa [b] using congrArg α h
  have hc2 : c ^ 2 = 1 := by
    have h : order48_G7_c ^ 2 = 1 := by decide
    simpa [c] using congrArg α h
  have hinj : Function.Injective F := by
    intro x y hxy
    apply α.injective
    simpa only [heval] using hxy
  have hmulIn : ∀ x y, F (x * y) = F x * F y := by
    intro x y
    rw [← heval, ← heval, ← heval]
    exact α.map_mul x y
  have hcube : ∀ x, F (F (F x)) = x := by
    intro x
    have hx := congrArg (fun β : MulAut order16_wild_G7 => β x)
      (order48_c3_action_generator_pow_three φ)
    rw [← heval (F (F x)), ← heval (F x), ← heval x]
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply,
      MulAut.one_apply] using hx
  have hne : ¬(a = order48_G7_a ∧ b = order48_G7_b ∧ c = order48_G7_c) := by
    intro h
    apply hφ
    apply MulEquiv.ext
    intro x
    rw [heval]
    dsimp [F]
    rw [h.1, h.2.1, h.2.2]
    change _ = (MonoidHom.id order16_wild_G7) x
    exact (order48_G7_hom_eval (MonoidHom.id order16_wild_G7) x).symm
  obtain ⟨u, v, w, huvw, hmul, hinter⟩ :=
    order48_G7_order_three_coordinates a b c ha4 hb2 hc2
      (hcube order48_G7_a) (hcube order48_G7_b) (hcube order48_G7_c)
      hne hinj hmulIn
  let T : order16_wild_G7 →* order16_wild_G7 :=
    { toFun := order48_G7_word u v w
      map_one' := by
        change order48_G7_word u v w 1 = 1
        simp [order48_G7_word]
      map_mul' := by
        intro x y
        exact hmul x y }
  let θ : MulAut order16_wild_G7 := MulEquiv.ofBijective T
    ⟨huvw, (Finite.injective_iff_surjective).mp huvw⟩
  refine ⟨θ, ?_⟩
  apply order48_c3_hom_ext
  apply MulEquiv.ext
  intro x
  change θ (α (θ.symm x)) = order48_RM_G7_tau3 x
  obtain ⟨y, rfl⟩ := θ.surjective x
  rw [θ.symm_apply_apply]
  change T (α y) = order48_RM_G7_tau3 (T y)
  change order48_G7_word u v w (α y) =
    order48_RM_G7_tau3 (order48_G7_word u v w y)
  rw [heval]
  rw [hinter y]
  simp only [order48_G7_word, map_mul, map_pow]

/-- Every compatible action on `G₇` yields the `C₄ × A₄` representative. -/
theorem order48_G7_action_complete : Order48WildKernelActionComplete 7 := by
  change ∀ φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G7,
    Nat.card {x : SemidirectProduct order16_wild_G7
      (Multiplicative (ZMod 3)) φ // x ^ 3 = 1} = 9 → _
  intro φ hRoots
  have hSyl := (order48_c3_action_card_sylow_three_eq_four_iff
    card_order16_wild_G7 φ).mpr hRoots
  have hne := order48_c3_action_generator_ne_one_of_card_sylow_four
    card_order16_wild_G7 φ hSyl
  obtain ⟨θ, hθ⟩ := order48_G7_action_conjugate φ hne
  exact order48_RM_G7_mem_residual_of_conj φ θ hθ

end Smallgroups.UsefulTheorems
