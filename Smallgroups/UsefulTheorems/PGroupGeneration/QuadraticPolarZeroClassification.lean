/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticSmallDimension

/-!
# Quadratic forms with zero polarization over `F₂`

Such a quadratic form is a linear functional. A vector on which the functional
is one splits the space into that coordinate and its kernel. Nonzero forms on
spaces of the same finite dimension are consequently isometric.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

variable {V W : Type*} [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]

/-- Split a nonzero linear functional into its value and its kernel coordinate. -/
def quadraticLinearFunctionalSplit (f : V →ₗ[F2] F2) (t : V) (ht : f t = 1) :
    V ≃ₗ[F2] F2 × f.ker where
  toFun v := (f v, ⟨v - f v • t, by
    change f (v - f v • t) = 0
    simp only [map_sub, map_smul, ht, smul_eq_mul, mul_one, sub_self]⟩)
  invFun z := z.1 • t + z.2.val
  left_inv v := by
    change f v • t + (v - f v • t) = v
    abel
  right_inv z := by
    have hk : f z.2.val = 0 := z.2.property
    have hv : f (z.1 • t + z.2.val) = z.1 := by
      simp only [map_add, map_smul, ht, hk, smul_eq_mul, mul_one, add_zero]
    apply Prod.ext
    · exact hv
    · apply Subtype.ext
      change z.1 • t + z.2.val - f (z.1 • t + z.2.val) • t = z.2.val
      rw [hv]
      abel
  map_add' u v := by
    apply Prod.ext
    · exact f.map_add u v
    · apply Subtype.ext
      change u + v - f (u + v) • t = (u - f u • t) + (v - f v • t)
      rw [f.map_add, add_smul]
      abel
  map_smul' a v := by
    apply Prod.ext
    · exact f.map_smul a v
    · apply Subtype.ext
      change a • v - f (a • v) • t = a • (v - f v • t)
      simp only [map_smul, smul_eq_mul, smul_sub, smul_smul]

@[simp] theorem quadraticLinearFunctionalSplit_fst (f : V →ₗ[F2] F2) (t : V)
    (ht : f t = 1) (v : V) : (quadraticLinearFunctionalSplit f t ht v).1 = f v := rfl

@[simp] theorem quadraticLinearFunctionalSplit_symm_value (f : V →ₗ[F2] F2) (t : V)
    (ht : f t = 1) (z : F2 × f.ker) :
    f ((quadraticLinearFunctionalSplit f t ht).symm z) = z.1 := by
  have hk : f z.2.val = 0 := z.2.property
  change f (z.1 • t + z.2.val) = z.1
  simp only [map_add, map_smul, ht, hk, smul_eq_mul, mul_one, add_zero]

private theorem polarZero_f2_eq_one (a : F2) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

/-- Nonzero zero-polar forms of the same finite dimension are isometric. -/
theorem quadraticPolarZero_equivalent_of_nonzero
    [FiniteDimensional F2 V] [FiniteDimensional F2 W]
    (Q : QuadraticMap F2 V F2) (R : QuadraticMap F2 W F2)
    (hBQ : Q.polarBilin = 0) (hBR : R.polarBilin = 0)
    (hQ : Q ≠ 0) (hR : R ≠ 0) (hdim : Module.finrank F2 V = Module.finrank F2 W) :
    Q.Equivalent R := by
  classical
  have hx : ∃ x, Q x ≠ 0 := by
    by_contra hn
    apply hQ
    apply DFunLike.ext
    intro x
    by_contra hx
    exact hn ⟨x, hx⟩
  have hy : ∃ y, R y ≠ 0 := by
    by_contra hn
    apply hR
    apply DFunLike.ext
    intro y
    by_contra hy
    exact hn ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  let f := quadraticLinearOfPolarZero Q hBQ
  let g := quadraticLinearOfPolarZero R hBR
  have hfx : f x = 1 := polarZero_f2_eq_one _ hx
  have hgy : g y = 1 := polarZero_f2_eq_one _ hy
  let eV := quadraticLinearFunctionalSplit f x hfx
  let eW := quadraticLinearFunctionalSplit g y hgy
  have hf := eV.finrank_eq
  have hg := eW.finrank_eq
  simp only [Module.finrank_prod, Module.finrank_self] at hf hg
  have hker : Module.finrank F2 f.ker = Module.finrank F2 g.ker := by omega
  let eK : f.ker ≃ₗ[F2] g.ker := LinearEquiv.ofFinrankEq f.ker g.ker hker
  let e : V ≃ₗ[F2] W := eV.trans
    ((LinearEquiv.prodCongr (LinearEquiv.refl F2 F2) eK).trans eW.symm)
  refine ⟨{ toLinearEquiv := e, map_app' := ?_ }⟩
  intro v
  change g ((quadraticLinearFunctionalSplit g y hgy).symm
    ((LinearEquiv.prodCongr (LinearEquiv.refl F2 F2) eK)
      (quadraticLinearFunctionalSplit f x hfx v))) = f v
  rw [quadraticLinearFunctionalSplit_symm_value]
  exact quadraticLinearFunctionalSplit_fst f x hfx v

end Smallgroups.UsefulTheorems.GF2Certificate
