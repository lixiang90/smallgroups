/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticCocycle

/-!
# Structural invariants of quadratic forms in characteristic two

In characteristic two, the kernel of the polar form need not equal the radical of
the quadratic form.  The former is the space on which the square function becomes
linear; the latter is the kernel of that restriction.  We keep these two subspaces
separate, and prove that their dimensions are preserved by quadratic isometries.

These invariants are necessary ingredients for a structural seven-form classification.
This file does not replace the existing orbit-completeness certificate.
-/

namespace QuadraticMap

variable {R V W P : Type*} [CommRing R] [AddCommGroup V] [AddCommGroup W]
  [AddCommGroup P] [Module R V] [Module R W] [Module R P]
  {Q : QuadraticMap R V P} {Q' : QuadraticMap R W P}

/-- A quadratic isometry preserves the polar pairing, also in characteristic two. -/
theorem IsometryEquiv.map_polarBilin (e : Q.IsometryEquiv Q') (x y : V) :
    Q'.polarBilin (e x) (e y) = Q.polarBilin x y := by
  simp only [polarBilin_apply_apply, polar, ← map_add e, e.map_app]

/-- Membership in the polar kernel is preserved by a quadratic isometry. -/
theorem IsometryEquiv.mem_ker_polarBilin (e : Q.IsometryEquiv Q') (x : V) :
    e x ∈ Q'.polarBilin.ker ↔ x ∈ Q.polarBilin.ker := by
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply]
  constructor
  · intro h y
    rw [← e.map_polarBilin x y]
    exact h (e y)
  · intro h y
    obtain ⟨z, rfl⟩ := e.toLinearEquiv.surjective y
    change Q'.polarBilin (e x) (e z) = 0
    rw [e.map_polarBilin]
    exact h z

/-- The polar kernel is transported exactly by a quadratic isometry. -/
theorem IsometryEquiv.map_ker_polarBilin (e : Q.IsometryEquiv Q') :
    Q.polarBilin.ker.map e.toLinearMap = Q'.polarBilin.ker := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (e.mem_ker_polarBilin x).2 hx
  · intro hy
    exact ⟨e.symm y, (e.symm.mem_ker_polarBilin y).2 hy, e.apply_symm_apply y⟩

/-- The dimension of the polar kernel is an invariant of a quadratic space. -/
theorem Equivalent.finrank_ker_polarBilin_eq (h : Q.Equivalent Q') :
    Module.finrank R Q.polarBilin.ker = Module.finrank R Q'.polarBilin.ker := by
  obtain ⟨e⟩ := h
  rw [← e.map_ker_polarBilin, LinearEquiv.finrank_map_eq]

/-- Vanishing of the quadratic map on its polar kernel is coordinate-independent. -/
theorem IsometryEquiv.vanishes_on_polar_ker_iff (e : Q.IsometryEquiv Q') :
    (∀ x ∈ Q.polarBilin.ker, Q x = 0) ↔
      (∀ y ∈ Q'.polarBilin.ker, Q' y = 0) := by
  constructor
  · intro h y hy
    have hx := (e.symm.mem_ker_polarBilin y).2 hy
    simpa only [e.symm.map_app] using h (e.symm y) hx
  · intro h x hx
    simpa only [e.map_app] using h (e x) ((e.mem_ker_polarBilin x).2 hx)

/-- A quadratic isometry restricts to an equivalence of the sets of zeros. -/
def IsometryEquiv.zeroFiberEquiv (e : Q.IsometryEquiv Q') :
    {x : V // Q x = 0} ≃ {y : W // Q' y = 0} :=
  e.toEquiv.subtypeEquiv fun x => by
    change Q x = 0 ↔ Q' (e x) = 0
    rw [e.map_app]

/-- The number of zeros is an invariant, usable to distinguish the two even-rank forms. -/
theorem Equivalent.card_zero_fiber_eq (h : Q.Equivalent Q') :
    Nat.card {x : V // Q x = 0} = Nat.card {y : W // Q' y = 0} := by
  obtain ⟨e⟩ := h
  exact Nat.card_congr e.zeroFiberEquiv

end QuadraticMap

namespace Smallgroups.UsefulTheorems.GF2Certificate

variable {V : Type*} [AddCommGroup V] [Module F2 V]

/-- Polarization of an `F₂` quadratic form is alternating. -/
theorem quadraticPolarBilin_self_eq_zero (Q : QuadraticMap F2 V F2) (x : V) :
    Q.polarBilin x x = 0 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul]
  exact ZModModule.add_self _

/-- Over `F₂`, a quadratic form restricts to a linear map on its polar kernel. -/
def quadraticPolarKernelRestriction (Q : QuadraticMap F2 V F2) :
    Q.polarBilin.ker →ₗ[F2] F2 where
  toFun x := Q x
  map_add' x y := by
    have hx := congrArg (fun f : V →ₗ[F2] F2 => f y) x.property
    simp only [LinearMap.zero_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar] at hx
    change Q (x.val + y.val) = Q x.val + Q y.val
    rw [sub_sub] at hx
    exact sub_eq_zero.mp hx
  map_smul' a x := by
    change Q (a • x.val) = a • Q x.val
    rw [Q.map_smul]
    have haa : a * a = a := by fin_cases a <;> rfl
    rw [haa]

@[simp] theorem quadraticPolarKernelRestriction_apply (Q : QuadraticMap F2 V F2)
    (x : Q.polarBilin.ker) : quadraticPolarKernelRestriction Q x = Q x :=
  rfl

/-- The quadratic radical is exactly the zero set of the restricted linear map. -/
theorem mem_quadratic_radical_iff (Q : QuadraticMap F2 V F2) (x : V) :
    x ∈ Q.radical ↔ ∃ hx : x ∈ Q.polarBilin.ker,
      quadraticPolarKernelRestriction Q ⟨x, hx⟩ = 0 := by
  change (Q x = 0 ∧ Q.polarBilin x = 0) ↔ _
  constructor
  · rintro ⟨hq, hp⟩
    exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact ⟨hq, hp⟩

end Smallgroups.UsefulTheorems.GF2Certificate
