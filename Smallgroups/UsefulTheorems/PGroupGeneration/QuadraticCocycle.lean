/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Smallgroups.UsefulTheorems.PGroupGeneration.Equivalences
import Smallgroups.UsefulTheorems.PGroupGeneration.GF2Certificate

/-!
# Quadratic forms attached to central `C₂` extensions

For an `F₂`-vector space `V` and a normalized central cocycle
`f : Multiplicative V → Multiplicative V → F₂`, the square of the canonical lift of `x`
has central coordinate `f x x`.  This is a quadratic form on `V`; its polar form is the
commutator pairing `f x y - f y x`.  The construction factors through cohomology and is
equivariant for linear changes of coordinates.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

private theorem f2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem add_self_eq_zero_of_f2_module {V : Type*} [AddCommGroup V] [Module F2 V]
    (x : V) : x + x = 0 := by
  have hchar : (1 : F2) + 1 = 0 := by decide
  calc
    x + x = (1 : F2) • x + (1 : F2) • x := by simp
    _ = ((1 : F2) + 1) • x := (add_smul (1 : F2) 1 x).symm
    _ = 0 := by rw [hchar, zero_smul]

private theorem xor_solve_right {V : Type*} [AddCommGroup V] [Module F2 V]
    {a b c d : V} (h : a + b = c + d) : b = a + c + d := by
  calc
    b = (a + a) + b := by rw [ZModModule.add_self, zero_add]
    _ = a + (a + b) := by ac_rfl
    _ = a + (c + d) := by rw [h]
    _ = a + c + d := by ac_rfl

private theorem xor_three_equations {V : Type*} [AddCommGroup V] [Module F2 V]
    {a b c d e f g h i : V} (h₁ : a + b = c + d) (h₂ : e + f = a + g)
    (h₃ : h + f = i + d) : b + g = h + e + c + i := by
  rw [xor_solve_right h₁, xor_solve_right h₂.symm, xor_solve_right h₃]
  calc
    (a + c + d) + (a + e + (h + i + d)) =
        (a + a) + (d + d) + (c + e + h + i) := by ac_rfl
    _ = c + e + h + i := by simp only [ZModModule.add_self, zero_add]
    _ = h + e + c + i := by ac_rfl

private theorem xor_polar_equations {V : Type*} [AddCommGroup V] [Module F2 V]
    {a b c d e f : V} (h₁ : a + b = c + d) (h₂ : e + 0 = f + c) :
    b + d + e = a + f := by
  rw [xor_solve_right h₁]
  have he : e = f + c := by simpa using h₂
  rw [he]
  calc
    (a + c + d) + d + (f + c) = (c + c) + (d + d) + (a + f) := by ac_rfl
    _ = a + f := by simp only [ZModModule.add_self, zero_add]

/-- The central coordinate of the square of the canonical lift of `x`. -/
def cocycleSquare {V : Type*} [AddCommGroup V] (f : Multiplicative V → Multiplicative V → F2)
    (x : V) : F2 :=
  f (Multiplicative.ofAdd x) (Multiplicative.ofAdd x)

/-- The central coordinate of the commutator of the canonical lifts of `x` and `y`. -/
def cocycleCommutator {V : Type*} [AddCommGroup V]
    (f : Multiplicative V → Multiplicative V → F2) (x y : V) : F2 :=
  f (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) -
    f (Multiplicative.ofAdd y) (Multiplicative.ofAdd x)

theorem cocycleCommutator_add_left {V : Type*} [AddCommGroup V]
    (f : Multiplicative V → Multiplicative V → F2) (hf : IsCentralCocycle f)
    (x x' y : V) :
    cocycleCommutator f (x + x') y =
      cocycleCommutator f x y + cocycleCommutator f x' y := by
  have h₁ := hf.cocycle (Multiplicative.ofAdd x) (Multiplicative.ofAdd x')
    (Multiplicative.ofAdd y)
  have h₂ := hf.cocycle (Multiplicative.ofAdd y) (Multiplicative.ofAdd x)
    (Multiplicative.ofAdd x')
  have h₃ := hf.cocycle (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)
    (Multiplicative.ofAdd x')
  simp only [← ofAdd_add] at h₁ h₂ h₃
  simp only [cocycleCommutator]
  rw [add_comm y x'] at h₃
  rw [add_comm y x] at h₂
  simp only [ZModModule.sub_eq_add]
  simpa only [add_assoc] using xor_three_equations h₁ h₂ h₃

theorem cocycleCommutator_smul_left {V : Type*} [AddCommGroup V] [Module F2 V]
    (f : Multiplicative V → Multiplicative V → F2) (hf : IsCentralCocycle f)
    (a : F2) (x y : V) :
    cocycleCommutator f (a • x) y = a • cocycleCommutator f x y := by
  rcases f2_eq_zero_or_one a with rfl | rfl <;>
    simp [cocycleCommutator, hf.one_left, hf.one_right]

private theorem cocycleSquare_polar {V : Type*} [AddCommGroup V] [Module F2 V]
    (f : Multiplicative V → Multiplicative V → F2) (hf : IsCentralCocycle f)
    (x y : V) :
    cocycleSquare f (x + y) - cocycleSquare f x - cocycleSquare f y =
      cocycleCommutator f x y := by
  have h₁ := hf.cocycle (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)
    (Multiplicative.ofAdd (x + y))
  have h₂ := hf.cocycle (Multiplicative.ofAdd y) (Multiplicative.ofAdd y)
    (Multiplicative.ofAdd x)
  simp only [← ofAdd_add] at h₁ h₂
  have hyy : y + y = 0 := add_self_eq_zero_of_f2_module y
  have hyxy : y + (x + y) = x := by
    calc
      y + (x + y) = x + (y + y) := by ac_rfl
      _ = x := by rw [hyy, add_zero]
  rw [hyxy] at h₁
  rw [hyy, add_comm y x] at h₂
  simp only [ofAdd_zero, hf.one_left] at h₁ h₂
  simp only [cocycleSquare, cocycleCommutator]
  simp only [ZModModule.sub_eq_add]
  exact xor_polar_equations h₁ h₂

/-- The square function of a central `C₂` extension, as a Mathlib quadratic form. -/
def cocycleQuadratic {V : Type*} [AddCommGroup V] [Module F2 V]
    (f : Multiplicative V → Multiplicative V → F2) (hf : IsCentralCocycle f) :
    QuadraticMap F2 V F2 :=
  QuadraticMap.ofPolar (cocycleSquare f)
    (by
      intro a x
      rcases f2_eq_zero_or_one a with rfl | rfl <;>
        simp [cocycleSquare, hf.one_left])
    (by
      intro x x' y
      simp only [QuadraticMap.polar]
      rw [cocycleSquare_polar f hf, cocycleSquare_polar f hf,
        cocycleSquare_polar f hf]
      exact cocycleCommutator_add_left f hf x x' y)
    (by
      intro a x y
      rcases f2_eq_zero_or_one a with rfl | rfl
      · simp [QuadraticMap.polar, cocycleSquare, ofAdd_zero, hf.one_left]
      · simp)

@[simp] theorem cocycleQuadratic_apply {V : Type*} [AddCommGroup V] [Module F2 V]
    (f : Multiplicative V → Multiplicative V → F2) (hf : IsCentralCocycle f) (x : V) :
    cocycleQuadratic f hf x = cocycleSquare f x :=
  rfl

/-- Polarization of the square form is exactly the commutator pairing. -/
theorem cocycleQuadratic_polar {V : Type*} [AddCommGroup V] [Module F2 V]
    (f : Multiplicative V → Multiplicative V → F2) (hf : IsCentralCocycle f) (x y : V) :
    QuadraticMap.polar (cocycleQuadratic f hf) x y = cocycleCommutator f x y := by
  simp only [QuadraticMap.polar, cocycleQuadratic_apply]
  exact cocycleSquare_polar f hf x y

/-- In the cocycle extension, the square of the canonical lift is the central element
selected by the quadratic form. -/
theorem canonicalLift_sq {V : Type*} [AddCommGroup V] [Module F2 V]
    (f : Multiplicative V → Multiplicative V → F2) (hf : IsCentralCocycle f) (x : V) :
    (⟨0, Multiplicative.ofAdd x⟩ : CocycleGroup f hf) ^ 2 =
      CocycleGroup.inl (hf := hf) (Multiplicative.ofAdd (cocycleQuadratic f hf x)) := by
  have hxx : x + x = 0 := add_self_eq_zero_of_f2_module x
  ext
  · simp [pow_two, cocycleSquare]
  · simp [pow_two, ← ofAdd_add, hxx]

/-- Adding a normalized coboundary does not change the square quadratic form. -/
theorem cocycleQuadratic_addCoboundary {V : Type*} [AddCommGroup V] [Module F2 V]
    (f : Multiplicative V → Multiplicative V → F2) (hf : IsCentralCocycle f)
    (d : Multiplicative V → F2) (hd : d 1 = 0) :
    cocycleQuadratic (addCoboundary f d) (hf.addCoboundary d hd) = cocycleQuadratic f hf := by
  ext x
  have hxx : x + x = 0 := add_self_eq_zero_of_f2_module x
  have hdouble : d (Multiplicative.ofAdd x) + d (Multiplicative.ofAdd x) = 0 :=
    add_self_eq_zero_of_f2_module _
  simp only [cocycleQuadratic_apply, cocycleSquare, addCoboundary, ← ofAdd_add,
    hxx, ofAdd_zero, hd, sub_zero]
  simpa using hdouble

/-- Pull a cocycle back along a linear endomorphism of its elementary-abelian base. -/
def pullbackCocycle {V W : Type*} [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W] (f : Multiplicative W → Multiplicative W → F2)
    (α : V →ₗ[F2] W) : Multiplicative V → Multiplicative V → F2 :=
  fun x y => f (Multiplicative.ofAdd (α x.toAdd)) (Multiplicative.ofAdd (α y.toAdd))

theorem pullbackCocycle_consistent {V W : Type*} [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W] (f : Multiplicative W → Multiplicative W → F2)
    (hf : IsCentralCocycle f) (α : V →ₗ[F2] W) :
    IsCentralCocycle (pullbackCocycle f α) := by
  let αm : Multiplicative V →* Multiplicative W :=
    { toFun := fun x => Multiplicative.ofAdd (α x.toAdd)
      map_one' := by simp
      map_mul' := by intro x y; simp }
  exact hf.comp αm

/-- The quadratic construction is equivariant for linear changes of base coordinates. -/
theorem cocycleQuadratic_pullback {V W : Type*} [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W] (f : Multiplicative W → Multiplicative W → F2)
    (hf : IsCentralCocycle f) (α : V →ₗ[F2] W) :
    cocycleQuadratic (pullbackCocycle f α) (pullbackCocycle_consistent f hf α) =
      (cocycleQuadratic f hf).comp α := by
  ext x
  rfl

end Smallgroups.UsefulTheorems.GF2Certificate
