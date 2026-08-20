/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.PresentedGroup
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeS4NormalForm

/-!
# Finite presentations for the four central double covers of `S₄`

The two signs are the common square of the adjacent lifts and the commutator
of the distant lifts.  The explicit normal form proves that each presentation
has at most 48 elements.
-/

namespace Smallgroups.UsefulTheorems

private def order48_s4CoverZ : FreeGroup (Fin 4) := FreeGroup.of 0
private def order48_s4CoverA : FreeGroup (Fin 4) := FreeGroup.of 1
private def order48_s4CoverB : FreeGroup (Fin 4) := FreeGroup.of 2
private def order48_s4CoverC : FreeGroup (Fin 4) := FreeGroup.of 3

/-- The ten relators for a normalized central double cover of `S₄`. -/
def order48_s4CoverRelations (squareSign commutatorSign : Fin 2) :
    Set (FreeGroup (Fin 4)) := fun r =>
  r = order48_s4CoverZ ^ 2 ∨
  r = order48_s4CoverZ * order48_s4CoverA * order48_s4CoverZ⁻¹ *
      order48_s4CoverA⁻¹ ∨
  r = order48_s4CoverZ * order48_s4CoverB * order48_s4CoverZ⁻¹ *
      order48_s4CoverB⁻¹ ∨
  r = order48_s4CoverZ * order48_s4CoverC * order48_s4CoverZ⁻¹ *
      order48_s4CoverC⁻¹ ∨
  r = order48_s4CoverA ^ 2 * (order48_s4CoverZ ^ squareSign.val)⁻¹ ∨
  r = order48_s4CoverB ^ 2 * (order48_s4CoverZ ^ squareSign.val)⁻¹ ∨
  r = order48_s4CoverC ^ 2 * (order48_s4CoverZ ^ squareSign.val)⁻¹ ∨
  r = (order48_s4CoverA * order48_s4CoverB) ^ 3 ∨
  r = (order48_s4CoverB * order48_s4CoverC) ^ 3 ∨
  r = order48_s4CoverA * order48_s4CoverC * order48_s4CoverA⁻¹ *
      order48_s4CoverC⁻¹ * (order48_s4CoverZ ^ commutatorSign.val)⁻¹

abbrev order48_s4CoverPresentation (squareSign commutatorSign : Fin 2) :=
  PresentedGroup (order48_s4CoverRelations squareSign commutatorSign)

private def order48_s4CoverPresentationGen
    (squareSign commutatorSign : Fin 2) :
    Fin 4 → order48_s4CoverPresentation squareSign commutatorSign :=
  PresentedGroup.of

private theorem order48_s4CoverPresentation_relations
    (squareSign commutatorSign : Fin 2) :
    let z := order48_s4CoverPresentationGen squareSign commutatorSign 0
    let a := order48_s4CoverPresentationGen squareSign commutatorSign 1
    let b := order48_s4CoverPresentationGen squareSign commutatorSign 2
    let c := order48_s4CoverPresentationGen squareSign commutatorSign 3
    z ^ 2 = 1 ∧
      z ∈ Subgroup.center (order48_s4CoverPresentation squareSign commutatorSign) ∧
      a ^ 2 = z ^ squareSign.val ∧ b ^ 2 = z ^ squareSign.val ∧
      c ^ 2 = z ^ squareSign.val ∧ (a * b) ^ 3 = 1 ∧ (b * c) ^ 3 = 1 ∧
      a * c * a⁻¹ * c⁻¹ = z ^ commutatorSign.val := by
  dsimp only
  let z : order48_s4CoverPresentation squareSign commutatorSign := PresentedGroup.of 0
  let a : order48_s4CoverPresentation squareSign commutatorSign := PresentedGroup.of 1
  let b : order48_s4CoverPresentation squareSign commutatorSign := PresentedGroup.of 2
  let c : order48_s4CoverPresentation squareSign commutatorSign := PresentedGroup.of 3
  have hrel (r : FreeGroup (Fin 4))
      (hr : r ∈ order48_s4CoverRelations squareSign commutatorSign) :
      PresentedGroup.mk (order48_s4CoverRelations squareSign commutatorSign) r = 1 :=
    PresentedGroup.one_of_mem hr
  have hz2 : z ^ 2 = 1 := by
    have h := hrel (order48_s4CoverZ ^ 2) (Or.inl rfl)
    exact h
  have hza : Commute z a := by
    have h := hrel (order48_s4CoverZ * order48_s4CoverA * order48_s4CoverZ⁻¹ *
      order48_s4CoverA⁻¹) (Or.inr (Or.inl rfl))
    change z * a * z⁻¹ * a⁻¹ = 1 at h
    apply eq_of_mul_inv_eq_one
    calc
      (z * a) * (a * z)⁻¹ = z * a * z⁻¹ * a⁻¹ := by group
      _ = 1 := h
  have hzb : Commute z b := by
    have h := hrel (order48_s4CoverZ * order48_s4CoverB * order48_s4CoverZ⁻¹ *
      order48_s4CoverB⁻¹) (Or.inr (Or.inr (Or.inl rfl)))
    change z * b * z⁻¹ * b⁻¹ = 1 at h
    apply eq_of_mul_inv_eq_one
    calc
      (z * b) * (b * z)⁻¹ = z * b * z⁻¹ * b⁻¹ := by group
      _ = 1 := h
  have hzc : Commute z c := by
    have h := hrel (order48_s4CoverZ * order48_s4CoverC * order48_s4CoverZ⁻¹ *
      order48_s4CoverC⁻¹) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    change z * c * z⁻¹ * c⁻¹ = 1 at h
    apply eq_of_mul_inv_eq_one
    calc
      (z * c) * (c * z)⁻¹ = z * c * z⁻¹ * c⁻¹ := by group
      _ = 1 := h
  have hzcenter : z ∈ Subgroup.center
      (order48_s4CoverPresentation squareSign commutatorSign) := by
    rw [Subgroup.mem_center_iff]
    intro x
    induction x using PresentedGroup.induction_on with
    | H w =>
      induction w using FreeGroup.induction_on with
      | C1 => exact Commute.one_left z
      | of i =>
          fin_cases i
          · exact Commute.refl z
          · exact hza.symm
          · exact hzb.symm
          · exact hzc.symm
      | inv_of i hi =>
          have hi' : Commute
              (PresentedGroup.mk (order48_s4CoverRelations squareSign commutatorSign)
                (FreeGroup.of i)) z := hi
          exact hi'.inv_left
      | mul x y hx hy =>
          have hx' : Commute
              (PresentedGroup.mk (order48_s4CoverRelations squareSign commutatorSign) x) z := hx
          have hy' : Commute
              (PresentedGroup.mk (order48_s4CoverRelations squareSign commutatorSign) y) z := hy
          exact hx'.mul_left hy'
  have ha2 : a ^ 2 = z ^ squareSign.val := by
    have h := hrel (order48_s4CoverA ^ 2 * (order48_s4CoverZ ^ squareSign.val)⁻¹)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    change a ^ 2 * (z ^ squareSign.val)⁻¹ = 1 at h
    exact mul_inv_eq_one.mp h
  have hb2 : b ^ 2 = z ^ squareSign.val := by
    have h := hrel (order48_s4CoverB ^ 2 * (order48_s4CoverZ ^ squareSign.val)⁻¹)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    change b ^ 2 * (z ^ squareSign.val)⁻¹ = 1 at h
    exact mul_inv_eq_one.mp h
  have hc2 : c ^ 2 = z ^ squareSign.val := by
    have h := hrel (order48_s4CoverC ^ 2 * (order48_s4CoverZ ^ squareSign.val)⁻¹)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    change c ^ 2 * (z ^ squareSign.val)⁻¹ = 1 at h
    exact mul_inv_eq_one.mp h
  have hab3 : (a * b) ^ 3 = 1 := by
    have h := hrel ((order48_s4CoverA * order48_s4CoverB) ^ 3)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    exact h
  have hbc3 : (b * c) ^ 3 = 1 := by
    have h := hrel ((order48_s4CoverB * order48_s4CoverC) ^ 3)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl rfl)))))))))
    exact h
  have hac : a * c * a⁻¹ * c⁻¹ = z ^ commutatorSign.val := by
    have h := hrel (order48_s4CoverA * order48_s4CoverC * order48_s4CoverA⁻¹ *
      order48_s4CoverC⁻¹ * (order48_s4CoverZ ^ commutatorSign.val)⁻¹)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr rfl)))))))))
    change a * c * a⁻¹ * c⁻¹ * (z ^ commutatorSign.val)⁻¹ = 1 at h
    exact mul_inv_eq_one.mp h
  exact ⟨hz2, hzcenter, ha2, hb2, hc2, hab3, hbc3, hac⟩

/-- Each of the four signed presentations has at most 48 elements. -/
theorem order48_s4CoverPresentation_finite_and_natCard_le
    (squareSign commutatorSign : Fin 2) :
    Finite (order48_s4CoverPresentation squareSign commutatorSign) ∧
      Nat.card (order48_s4CoverPresentation squareSign commutatorSign) ≤ 48 := by
  let z := order48_s4CoverPresentationGen squareSign commutatorSign 0
  let a := order48_s4CoverPresentationGen squareSign commutatorSign 1
  let b := order48_s4CoverPresentationGen squareSign commutatorSign 2
  let c := order48_s4CoverPresentationGen squareSign commutatorSign 3
  obtain ⟨hz2, hzcenter, ha2, hb2, hc2, hab3, hbc3, hac⟩ :=
    order48_s4CoverPresentation_relations squareSign commutatorSign
  apply finite_and_natCard_le_48_of_s4_signed_coxeter_generators a b c z squareSign
    commutatorSign hzcenter hz2 ha2 hb2 hc2 hab3 hbc3 hac
  have hgenEq : order48_s4SignedGen z a b c =
      order48_s4CoverPresentationGen squareSign commutatorSign := by
    funext i
    fin_cases i <;> rfl
  rw [hgenEq]
  change Subgroup.closure (Set.range (PresentedGroup.of : Fin 4 →
    order48_s4CoverPresentation squareSign commutatorSign)) = ⊤
  exact PresentedGroup.closure_range_of _

theorem order48_s4CoverPresentation_natCard_le
    (squareSign commutatorSign : Fin 2) :
    Nat.card (order48_s4CoverPresentation squareSign commutatorSign) ≤ 48 :=
  (order48_s4CoverPresentation_finite_and_natCard_le squareSign commutatorSign).2

section Recognition

variable {H : Type*} [Group H] (z a b c : H)

private theorem order48_s4CoverRelations_hold
    (squareSign commutatorSign : Fin 2)
    (hzcenter : z ∈ Subgroup.center H) (hz2 : z ^ 2 = 1)
    (ha : a ^ 2 = z ^ squareSign.val)
    (hb : b ^ 2 = z ^ squareSign.val)
    (hc : c ^ 2 = z ^ squareSign.val)
    (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1)
    (hac : a * c * a⁻¹ * c⁻¹ = z ^ commutatorSign.val) :
    ∀ r ∈ order48_s4CoverRelations squareSign commutatorSign,
      FreeGroup.lift (order48_s4SignedGen z a b c) r = 1 := by
  have hzcomm (x : H) : Commute z x :=
    (Subgroup.mem_center_iff.mp hzcenter x).symm
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [order48_s4CoverZ, order48_s4SignedGen] using hz2
  · simp only [order48_s4CoverZ, order48_s4CoverA, map_mul, FreeGroup.lift_apply_of,
      map_inv, order48_s4SignedGen]
    rw [(hzcomm a).eq]
    group
  · simp only [order48_s4CoverZ, order48_s4CoverB, map_mul, FreeGroup.lift_apply_of,
      map_inv, order48_s4SignedGen]
    rw [(hzcomm b).eq]
    group
  · simp only [order48_s4CoverZ, order48_s4CoverC, map_mul, FreeGroup.lift_apply_of,
      map_inv, order48_s4SignedGen]
    rw [(hzcomm c).eq]
    group
  · simp only [order48_s4CoverA, order48_s4CoverZ, map_mul, map_pow,
      FreeGroup.lift_apply_of, map_inv, order48_s4SignedGen]
    rw [ha]
    group
  · simp only [order48_s4CoverB, order48_s4CoverZ, map_mul, map_pow,
      FreeGroup.lift_apply_of, map_inv, order48_s4SignedGen]
    rw [hb]
    group
  · simp only [order48_s4CoverC, order48_s4CoverZ, map_mul, map_pow,
      FreeGroup.lift_apply_of, map_inv, order48_s4SignedGen]
    rw [hc]
    group
  · simpa [order48_s4CoverA, order48_s4CoverB, order48_s4SignedGen] using hab
  · simpa [order48_s4CoverB, order48_s4CoverC, order48_s4SignedGen] using hbc
  · simp only [order48_s4CoverA, order48_s4CoverC, order48_s4CoverZ, map_mul,
      FreeGroup.lift_apply_of, map_inv, map_pow, order48_s4SignedGen]
    rw [hac]
    group

/-- The universal homomorphism from the signed presentation. -/
def order48_s4CoverToGroup
    (squareSign commutatorSign : Fin 2)
    (hzcenter : z ∈ Subgroup.center H) (hz2 : z ^ 2 = 1)
    (ha : a ^ 2 = z ^ squareSign.val)
    (hb : b ^ 2 = z ^ squareSign.val)
    (hc : c ^ 2 = z ^ squareSign.val)
    (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1)
    (hac : a * c * a⁻¹ * c⁻¹ = z ^ commutatorSign.val) :
    order48_s4CoverPresentation squareSign commutatorSign →* H :=
  PresentedGroup.toGroup
    (order48_s4CoverRelations_hold z a b c squareSign commutatorSign
      hzcenter hz2 ha hb hc hab hbc hac)

theorem order48_s4CoverToGroup_surjective
    (squareSign commutatorSign : Fin 2)
    (hzcenter : z ∈ Subgroup.center H) (hz2 : z ^ 2 = 1)
    (ha : a ^ 2 = z ^ squareSign.val)
    (hb : b ^ 2 = z ^ squareSign.val)
    (hc : c ^ 2 = z ^ squareSign.val)
    (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1)
    (hac : a * c * a⁻¹ * c⁻¹ = z ^ commutatorSign.val)
    (hgen : Subgroup.closure (Set.range (order48_s4SignedGen z a b c)) = ⊤) :
    Function.Surjective (order48_s4CoverToGroup z a b c squareSign commutatorSign
      hzcenter hz2 ha hb hc hab hbc hac) := by
  rw [← MonoidHom.range_eq_top]
  apply le_antisymm le_top
  rw [← hgen]
  rw [Subgroup.closure_le]
  rintro x ⟨i, rfl⟩
  refine ⟨PresentedGroup.of i, ?_⟩
  simp [order48_s4CoverToGroup]

/-- A 48-element group generated by a normalized signed Coxeter quadruple is
isomorphic to the corresponding presentation. -/
theorem nonempty_mulEquiv_s4CoverPresentation_of_card
    [Finite H] (hcard : Nat.card H = 48)
    (squareSign commutatorSign : Fin 2)
    (hzcenter : z ∈ Subgroup.center H) (hz2 : z ^ 2 = 1)
    (ha : a ^ 2 = z ^ squareSign.val)
    (hb : b ^ 2 = z ^ squareSign.val)
    (hc : c ^ 2 = z ^ squareSign.val)
    (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1)
    (hac : a * c * a⁻¹ * c⁻¹ = z ^ commutatorSign.val)
    (hgen : Subgroup.closure (Set.range (order48_s4SignedGen z a b c)) = ⊤) :
    Nonempty (order48_s4CoverPresentation squareSign commutatorSign ≃* H) := by
  let φ := order48_s4CoverToGroup z a b c squareSign commutatorSign
    hzcenter hz2 ha hb hc hab hbc hac
  have hsurj : Function.Surjective φ := order48_s4CoverToGroup_surjective
    z a b c squareSign commutatorSign hzcenter hz2 ha hb hc hab hbc hac hgen
  letI : Finite (order48_s4CoverPresentation squareSign commutatorSign) :=
    (order48_s4CoverPresentation_finite_and_natCard_le squareSign commutatorSign).1
  have hle := order48_s4CoverPresentation_natCard_le squareSign commutatorSign
  have hge : 48 ≤ Nat.card (order48_s4CoverPresentation squareSign commutatorSign) := by
    rw [← hcard]
    exact Nat.card_le_card_of_surjective φ hsurj
  have hPcard : Nat.card (order48_s4CoverPresentation squareSign commutatorSign) = 48 :=
    le_antisymm hle hge
  have hbij : Function.Bijective φ :=
    hsurj.bijective_of_nat_card_le (by rw [hPcard, hcard])
  exact ⟨MulEquiv.ofBijective φ hbij⟩

end Recognition

end Smallgroups.UsefulTheorems
