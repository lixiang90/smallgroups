/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeRMExamples
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionClassifiers

/-!
# The `G₈ = D₈ × C₂` residual action

An automorphism of `G₈` is determined by the images of its standard rotation,
central involution, and reflection.  A small coordinate calculation proves that
an automorphism whose cube is the identity fixes all three generators.  Thus
`Aut(G₈)` has no nontrivial element of order three, and the four-Sylow-three
residual branch with kernel `G₈` is empty.
-/

namespace Smallgroups.UsefulTheorems

private noncomputable def order48_G8_word
    (a b c x : order16_wild_G8) : order16_wild_G8 :=
  a ^ (Multiplicative.toAdd x.left.1).val *
    b ^ (Multiplicative.toAdd x.left.2).val *
    c ^ (Multiplicative.toAdd x.right).val

private noncomputable def order48_G8_decidableForallThree
    {α : Type*} [Fintype α]
    (p : α → α → α → Prop) (hp : ∀ a b c, Decidable (p a b c)) :
    Decidable (∀ a b c, p a b c) :=
  @Fintype.decidableForallFintype α (fun a => ∀ b c, p a b c)
    (fun a => @Fintype.decidableForallFintype α (fun b => ∀ c, p a b c)
      (fun b => @Fintype.decidableForallFintype α (p a b)
        (fun c => hp a b c) inferInstance) inferInstance) inferInstance

private def order48_G8_decidableImp {p q : Prop}
    (hp : Decidable p) (hq : Decidable q) : Decidable (p → q) :=
  match hp, hq with
  | isFalse hp, _ => isTrue (fun h => False.elim (hp h))
  | isTrue _, isTrue hq => isTrue (fun _ => hq)
  | isTrue hp, isFalse hq => isFalse (fun h => hq (h hp))

private noncomputable def order48_G8_coordinateRigidity : Prop :=
  ∀ a b c : order16_wild_G8,
    a ^ 4 = 1 →
    b ^ 2 = 1 →
    c ^ 2 = 1 →
    b * a = a * b →
    b * c = c * b →
    c * a * c = a⁻¹ →
    order48_G8_word a b c
      (order48_G8_word a b c
        (order48_G8_word a b c order48_RM_G8_r)) = order48_RM_G8_r →
    order48_G8_word a b c
      (order48_G8_word a b c
        (order48_G8_word a b c order48_RM_G8_s)) = order48_RM_G8_s →
    order48_G8_word a b c
      (order48_G8_word a b c
        (order48_G8_word a b c order48_RM_G8_t)) = order48_RM_G8_t →
    (∀ x, order48_G8_word a b c x = 1 → x = 1) →
    a = order48_RM_G8_r ∧ b = order48_RM_G8_s ∧ c = order48_RM_G8_t

private noncomputable def order48_G8_coordinateRigidity_decidable :
    Decidable order48_G8_coordinateRigidity :=
  order48_G8_decidableForallThree _ (fun a b c => by
    have ha4 : Decidable (a ^ 4 = 1) := inferInstance
    have hb2 : Decidable (b ^ 2 = 1) := inferInstance
    have hc2 : Decidable (c ^ 2 = 1) := inferInstance
    have hba : Decidable (b * a = a * b) := inferInstance
    have hbc : Decidable (b * c = c * b) := inferInstance
    have hcar : Decidable (c * a * c = a⁻¹) := inferInstance
    have hca : Decidable (order48_G8_word a b c
        (order48_G8_word a b c
          (order48_G8_word a b c order48_RM_G8_r)) = order48_RM_G8_r) :=
      inferInstance
    have hcb : Decidable (order48_G8_word a b c
        (order48_G8_word a b c
          (order48_G8_word a b c order48_RM_G8_s)) = order48_RM_G8_s) :=
      inferInstance
    have hcc : Decidable (order48_G8_word a b c
        (order48_G8_word a b c
          (order48_G8_word a b c order48_RM_G8_t)) = order48_RM_G8_t) :=
      inferInstance
    have hk : Decidable (∀ x, order48_G8_word a b c x = 1 → x = 1) :=
      inferInstance
    have heq : Decidable
        (a = order48_RM_G8_r ∧ b = order48_RM_G8_s ∧ c = order48_RM_G8_t) :=
      inferInstance
    exact order48_G8_decidableImp ha4 <| order48_G8_decidableImp hb2 <|
      order48_G8_decidableImp hc2 <| order48_G8_decidableImp hba <|
      order48_G8_decidableImp hbc <| order48_G8_decidableImp hcar <|
      order48_G8_decidableImp hca <| order48_G8_decidableImp hcb <|
      order48_G8_decidableImp hcc <| order48_G8_decidableImp hk heq)

set_option maxHeartbeats 1600000 in
-- Kernel evaluation checks the finite generator-image table for `D₈ × C₂`.
private theorem order48_G8_coordinateRigidity_proof :
    order48_G8_coordinateRigidity := by
  exact @of_decide_eq_true order48_G8_coordinateRigidity
    order48_G8_coordinateRigidity_decidable (by decide +kernel)

private theorem order48_G8_aut_cube_eq_one
    (α : MulAut order16_wild_G8) (hcube : α ^ 3 = 1) : α = 1 := by
  let a := α order48_RM_G8_r
  let b := α order48_RM_G8_s
  let c := α order48_RM_G8_t
  let F := order48_G8_word a b c
  have heval : ∀ x, α x = F x := order48_RM_G8_hom_eval α.toMonoidHom
  have ha4 : a ^ 4 = 1 := by
    have h : order48_RM_G8_r ^ 4 = 1 := by decide
    simpa [a] using congrArg α h
  have hb2 : b ^ 2 = 1 := by
    have h : order48_RM_G8_s ^ 2 = 1 := by decide
    simpa [b] using congrArg α h
  have hc2 : c ^ 2 = 1 := by
    have h : order48_RM_G8_t ^ 2 = 1 := by decide
    simpa [c] using congrArg α h
  have hba : b * a = a * b := by
    have h : order48_RM_G8_s * order48_RM_G8_r =
        order48_RM_G8_r * order48_RM_G8_s := by decide
    simpa [a, b] using congrArg α h
  have hbc : b * c = c * b := by
    have h : order48_RM_G8_s * order48_RM_G8_t =
        order48_RM_G8_t * order48_RM_G8_s := by decide
    simpa [b, c] using congrArg α h
  have hcar : c * a * c = a⁻¹ := by
    have h : order48_RM_G8_t * order48_RM_G8_r * order48_RM_G8_t =
        order48_RM_G8_r⁻¹ := by decide
    simpa [a, c] using congrArg α h
  have hcubeF : ∀ x, F (F (F x)) = x := by
    intro x
    have hx := congrArg (fun β : MulAut order16_wild_G8 => β x) hcube
    rw [← heval (F (F x)), ← heval (F x), ← heval x]
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply,
      MulAut.one_apply] using hx
  have hker : ∀ x, F x = 1 → x = 1 := by
    intro x hx
    apply α.injective
    rw [heval]
    simpa only [map_one] using hx
  obtain ⟨ha, hb, hc⟩ := order48_G8_coordinateRigidity_proof a b c
    ha4 hb2 hc2 hba hbc hcar
    (hcubeF order48_RM_G8_r) (hcubeF order48_RM_G8_s)
    (hcubeF order48_RM_G8_t) hker
  apply MulEquiv.ext
  intro x
  rw [heval]
  dsimp [F]
  rw [ha, hb, hc]
  change _ = (MonoidHom.id order16_wild_G8) x
  exact (order48_RM_G8_hom_eval (MonoidHom.id order16_wild_G8) x).symm

/-- The four-Sylow-three residual branch with kernel `G₈` is empty. -/
theorem order48_G8_action_complete : Order48WildKernelActionComplete 8 := by
  change ∀ φ : Multiplicative (ZMod 3) →* MulAut order16_wild_G8,
    Nat.card {x : SemidirectProduct order16_wild_G8
      (Multiplicative (ZMod 3)) φ // x ^ 3 = 1} = 9 → _
  intro φ hRoots
  have hSyl := (order48_c3_action_card_sylow_three_eq_four_iff
    card_order16_wild_G8 φ).mpr hRoots
  have hne := order48_c3_action_generator_ne_one_of_card_sylow_four
    card_order16_wild_G8 φ hSyl
  exact (hne (order48_G8_aut_cube_eq_one _
    (order48_c3_action_generator_pow_three φ))).elim

end Smallgroups.UsefulTheorems
