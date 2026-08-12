/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeActionCore

/-!
# Orbit infrastructure for the residual `C₃` actions

The RM and RN reductions leave actions of `C₃` on concrete Wild groups of
order `16`.  This file isolates the common orbit move: conjugating the action
by an automorphism of the kernel and precomposing it by an automorphism of the
complement both preserve the semidirect-product isomorphism class.
-/

namespace Smallgroups.UsefulTheorems

private noncomputable def order48_c3_generator : Multiplicative (ZMod 3) :=
  Multiplicative.ofAdd (1 : ZMod 3)

private theorem order48_c3_generator_span
    (x : Multiplicative (ZMod 3)) :
    x = order48_c3_generator ^ (Multiplicative.toAdd x).val := by
  revert x
  decide

/-- Homomorphisms out of `C₃` are determined by the standard generator. -/
theorem order48_c3_hom_ext {M : Type*} [Monoid M]
    {φ ψ : Multiplicative (ZMod 3) →* M}
    (h : φ order48_c3_generator = ψ order48_c3_generator) : φ = ψ := by
  apply MonoidHom.ext
  intro x
  rw [order48_c3_generator_span x, map_pow, map_pow, h]

/-- Moving a `C₃` action by an automorphism of its order-`16` kernel gives an
isomorphic semidirect product. -/
theorem order48_c3_action_conj_orbit_move
    {K : Type*} [Group K]
    {φ ψ : Multiplicative (ZMod 3) →* MulAut K}
    (θ : K ≃* K)
    (h : (MulAut.conj θ).toMonoidHom.comp φ = ψ) :
    Nonempty (SemidirectProduct K (Multiplicative (ZMod 3)) φ ≃*
      SemidirectProduct K (Multiplicative (ZMod 3)) ψ) := by
  exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans
    (semidirectProductCongr_eq h)⟩

/-- Moving a `C₃` action by an automorphism of the complement gives an
isomorphic semidirect product. -/
theorem order48_c3_action_precomp_orbit_move
    {K : Type*} [Group K]
    {φ ψ : Multiplicative (ZMod 3) →* MulAut K}
    (σ : Multiplicative (ZMod 3) ≃* Multiplicative (ZMod 3))
    (h : φ.comp σ.toMonoidHom = ψ) :
    Nonempty (SemidirectProduct K (Multiplicative (ZMod 3)) φ ≃*
      SemidirectProduct K (Multiplicative (ZMod 3)) ψ) := by
  exact ⟨(semidirectProductCongrAut (N := K) (φ := φ) σ).symm.trans
    (semidirectProductCongr_eq (N := K)
      (φ := φ.comp σ.toMonoidHom) (ψ := ψ) h)⟩

/-- The finite orbit-completeness statement needed for a fixed Wild kernel. -/
def Order48C3ActionOrbitComplete
    (K : Type*) [Group K] (m : ℕ)
    (rep : Fin m → Multiplicative (ZMod 3) →* MulAut K) : Prop :=
  ∀ φ : Multiplicative (ZMod 3) →* MulAut K,
    ∃ i : Fin m,
      Nonempty (SemidirectProduct K (Multiplicative (ZMod 3)) φ ≃*
        SemidirectProduct K (Multiplicative (ZMod 3)) (rep i))

theorem order48_c3_action_orbit_complete_of_generator_cases
    {K : Type*} [Group K] {m : ℕ}
    (rep : Fin m → Multiplicative (ZMod 3) →* MulAut K)
    (hcases : ∀ φ : Multiplicative (ZMod 3) →* MulAut K,
      ∃ i : Fin m, ∃ θ : K ≃* K,
        (MulAut.conj θ).toMonoidHom.comp φ = rep i) :
    Order48C3ActionOrbitComplete K m rep := by
  intro φ
  obtain ⟨i, θ, hθ⟩ := hcases φ
  exact ⟨i, order48_c3_action_conj_orbit_move θ hθ⟩

end Smallgroups.UsefulTheorems
