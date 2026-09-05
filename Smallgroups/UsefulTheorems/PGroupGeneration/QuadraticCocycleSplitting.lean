/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticCocycle

/-!
# The square form detects central cohomology over an elementary abelian base

A central `C₂` cocycle with zero square form defines an abelian extension of
exponent two. Its projection is therefore a surjective linear map of `F₂` vector
spaces and admits a linear section. The central coordinate of this section
expresses the cocycle as a coboundary.

Consequently, two cocycles have the same square quadratic form precisely when
they differ by a normalized coboundary. No finite enumeration or dimension
assumption is needed.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

variable {V : Type*} [AddCommGroup V] [Module F2 V]

/-- A cocycle with zero diagonal on an elementary abelian group is a coboundary.
The proof splits its extension as a sequence of vector spaces over `F₂`. -/
theorem exists_centralCoboundary_of_diagonal_zero
    (f : Multiplicative V → Multiplicative V → F2) (hf : IsCentralCocycle f)
    (hdiag : ∀ x, f x x = 0) :
    ∃ d : Multiplicative V → F2, d 1 = 0 ∧
      f = centralCoboundary (Multiplicative V) F2 d := by
  classical
  have hsym (a b : Multiplicative V) : f a b = f b a := by
    apply sub_eq_zero.mp
    change cocycleCommutator f a.toAdd b.toAdd = 0
    rw [← cocycleQuadratic_polar f hf]
    simp [QuadraticMap.polar, cocycleSquare, hdiag]
  let E := CocycleGroup f hf
  letI : CommGroup E :=
    { (inferInstance : Group E) with
      mul_comm := by
        intro x y
        apply CocycleGroup.ext
        · change x.fst + y.fst + f x.snd y.snd =
            y.fst + x.fst + f y.snd x.snd
          rw [hsym x.snd y.snd, add_comm x.fst y.fst]
        · exact mul_comm x.snd y.snd }
  have htwo (x : E) : x * x = 1 := by
    apply CocycleGroup.ext
    · change x.fst + x.fst + f x.snd x.snd = 0
      simp only [ZModModule.add_self, hdiag]
    · change x.snd.toAdd + x.snd.toAdd = (0 : V)
      exact ZModModule.add_self _
  letI : Module F2 (Additive E) :=
    AddCommGroup.zmodModule (n := 2) (fun x => by
      rw [two_nsmul]
      change x.toMul * x.toMul = 1
      exact htwo x.toMul)
  let p : Additive E →ₗ[F2] V :=
    (CocycleGroup.rightHom (hf := hf)).toAdditiveLeft.toZModLinearMap 2
  have hp : Function.Surjective p := by
    intro x
    exact ⟨Additive.ofMul ⟨0, Multiplicative.ofAdd x⟩, rfl⟩
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  have hsnd (x : V) : (s x).toMul.snd = Multiplicative.ofAdd x := by
    have hx := DFunLike.congr_fun hs x
    change (s x).toMul.snd.toAdd = x at hx
    exact congrArg Multiplicative.ofAdd hx
  let t : V → F2 := fun x => (s x).toMul.fst
  have ht0 : t 0 = 0 := by
    change (s 0).toMul.fst = 0
    rw [map_zero]
    rfl
  have htadd (x y : V) :
      t (x + y) = t x + t y + f (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) := by
    have h := congrArg (fun z : Additive E => z.toMul.fst) (s.map_add x y)
    change t (x + y) = t x + t y + f (s x).toMul.snd (s y).toMul.snd at h
    simpa only [hsnd] using h
  refine ⟨fun x => -t x.toAdd, ?_, ?_⟩
  · change -t 0 = 0
    rw [ht0, neg_zero]
  · funext a b
    change f a b = -t a.toAdd + -t b.toAdd - -t (a.toAdd + b.toAdd)
    rw [htadd]
    abel

/-- The square quadratic form is a complete invariant of the central cohomology
class when the base is a vector space over `F₂`. -/
theorem cocycleQuadratic_eq_iff_addCoboundary
    (f g : Multiplicative V → Multiplicative V → F2)
    (hf : IsCentralCocycle f) (hg : IsCentralCocycle g) :
    cocycleQuadratic f hf = cocycleQuadratic g hg ↔
      ∃ d : Multiplicative V → F2, d 1 = 0 ∧ f = addCoboundary g d := by
  constructor
  · intro hq
    have hfg : IsCentralCocycle (fun a b => f a b - g a b) :=
      (centralCocycles (Multiplicative V) F2).sub_mem hf hg
    have hdiag (a : Multiplicative V) : f a a - g a a = 0 := by
      apply sub_eq_zero.mpr
      exact congrArg (fun q : QuadraticMap F2 V F2 => q a.toAdd) hq
    obtain ⟨d, hd, hdiff⟩ :=
      exists_centralCoboundary_of_diagonal_zero _ hfg hdiag
    refine ⟨d, hd, ?_⟩
    funext a b
    have hab := congrFun (congrFun hdiff a) b
    change f a b = g a b + centralCoboundary (Multiplicative V) F2 d a b
    rw [← hab]
    abel
  · rintro ⟨d, hd, rfl⟩
    exact cocycleQuadratic_addCoboundary g hg d hd

/-- Equal square quadratic forms give isomorphic central extensions. -/
theorem nonempty_cocycleGroup_mulEquiv_of_cocycleQuadratic_eq
    (f g : Multiplicative V → Multiplicative V → F2)
    (hf : IsCentralCocycle f) (hg : IsCentralCocycle g)
    (hq : cocycleQuadratic f hf = cocycleQuadratic g hg) :
    Nonempty (CocycleGroup f hf ≃* CocycleGroup g hg) := by
  obtain ⟨d, hd, hfg⟩ := (cocycleQuadratic_eq_iff_addCoboundary f g hf hg).mp hq
  subst f
  exact ⟨CocycleGroup.coboundaryEquiv hg d hd⟩

/-- Isometric square quadratic forms give isomorphic central extensions, including
when the two elementary abelian bases use different vector-space carriers. -/
theorem nonempty_cocycleGroup_mulEquiv_of_cocycleQuadratic_equivalent
    {W : Type*} [AddCommGroup W] [Module F2 W]
    (f : Multiplicative V → Multiplicative V → F2)
    (g : Multiplicative W → Multiplicative W → F2)
    (hf : IsCentralCocycle f) (hg : IsCentralCocycle g)
    (hq : (cocycleQuadratic f hf).Equivalent (cocycleQuadratic g hg)) :
    Nonempty (CocycleGroup f hf ≃* CocycleGroup g hg) := by
  obtain ⟨e⟩ := hq
  let g' := pullbackCocycle g e.toLinearEquiv.toLinearMap
  let hg' := pullbackCocycle_consistent g hg e.toLinearEquiv.toLinearMap
  have heq : cocycleQuadratic f hf = cocycleQuadratic g' hg' := by
    change cocycleQuadratic f hf = cocycleQuadratic
      (pullbackCocycle g e.toLinearEquiv.toLinearMap)
      (pullbackCocycle_consistent g hg e.toLinearEquiv.toLinearMap)
    rw [cocycleQuadratic_pullback g hg e.toLinearEquiv.toLinearMap]
    ext x
    exact (e.map_app x).symm
  obtain ⟨i⟩ := nonempty_cocycleGroup_mulEquiv_of_cocycleQuadratic_eq f g' hf hg' heq
  let α : Multiplicative V ≃* Multiplicative W :=
    e.toLinearEquiv.toAddEquiv.toMultiplicative
  exact ⟨i.trans (CocycleGroup.congrRight hg α)⟩

end Smallgroups.UsefulTheorems.GF2Certificate
