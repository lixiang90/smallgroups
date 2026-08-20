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

private def order48_G7_coordinateComplete : Prop :=
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
    (∀ x y, order48_G7_word a b c x =
      order48_G7_word a b c y → x = y) →
    (∀ x y, order48_G7_word a b c (x * y) =
      order48_G7_word a b c x * order48_G7_word a b c y) →
    ∃ u v w, order48_G7_conjugacyWitness a b c u v w

private def order48_G7_coordinateComplete_decidable :
    Decidable order48_G7_coordinateComplete :=
  order48_decidableForallThree _ (fun a b c => by
    let q := order48_G7_conjugacyWitness a b c
    let hq : Decidable (∃ u v w, q u v w) :=
      order48_decidableExistsThree q (fun _ _ _ => by
        dsimp [q, order48_G7_conjugacyWitness]
        infer_instance)
    letI := hq
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
    have hi : Decidable (∀ x y, order48_G7_word a b c x =
        order48_G7_word a b c y → x = y) := inferInstance
    have hm : Decidable (∀ x y, order48_G7_word a b c (x * y) =
        order48_G7_word a b c x * order48_G7_word a b c y) := inferInstance
    have hn : Decidable
        (¬(a = order48_G7_a ∧ b = order48_G7_b ∧ c = order48_G7_c)) :=
      inferInstance
    exact order48_decidableImp ha4 <| order48_decidableImp hb2 <|
      order48_decidableImp hc2 <| order48_decidableImp hca <|
      order48_decidableImp hcb <| order48_decidableImp hcc <|
      order48_decidableImp hn <| order48_decidableImp hi <|
      order48_decidableImp hm hq)

private def order48_G7_coordinateComplete_check : Bool :=
  @decide order48_G7_coordinateComplete order48_G7_coordinateComplete_decidable

private theorem order48_G7_coordinateComplete_proof :
    order48_G7_coordinateComplete := by
  exact @of_decide_eq_true order48_G7_coordinateComplete
    order48_G7_coordinateComplete_decidable (by
  change order48_G7_coordinateComplete_check = true
  native_decide)

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
    (hmulIn : ∀ x y, order48_G7_word a b c (x * y) =
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
  obtain ⟨u, v, w, _, _, _, hinj', hmul', hinter⟩ :=
    order48_G7_coordinateComplete_proof a b c ha4 hb2 hc2
      hcubeA hcubeB hcubeC hne hinj hmulIn
  exact ⟨u, v, w, hinj', hmul', hinter⟩

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
