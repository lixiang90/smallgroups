/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.End

/-!
# Classifying semidirect products by their action

After `SchurZassenhaus.lean` writes a group as `N ⋊[φ] H`, classification reduces to understanding
which actions `φ : H →* MulAut N` give isomorphic groups. This file develops the tools.

The action `φ` is recovered from the group together with its canonical inclusions by
`φ h n = (inr h * inl n * (inr h)⁻¹).left` (`SemidirectProduct.conjAction_eq`), so the
parametrisation is **faithful**: an isomorphism fixing `inl` and `inr` forces `φ = ψ`
(`semidirectProduct_action_inj`).

Two actions give *isomorphic* groups when they lie in the same orbit of `Aut N × Aut H` acting on
`Hom(H, Aut N)` by `(θ, σ) • φ = θ ∘ φ ∘ σ⁻¹` (up to conjugation). The constructive direction is:

* `semidirectProductCongr` — the master constructor: from `θ : N ≃* N'`, `σ : H ≃* H'` and a
  compatibility condition, build `N ⋊[φ] H ≃* N' ⋊[φ'] H'`;
* `semidirectProductCongrAut` — precomposing `φ` with an automorphism of `H` gives an isomorphic
  group;
* `semidirectProductCongrConj` — conjugating the action `φ` by an automorphism `θ` of `N` gives an
  isomorphic group;
* `semidirectProductCongr_eq` — equal actions give (canonically) isomorphic groups.

Together with the faithfulness statement, these reduce the isomorphism problem for `N ⋊ H` to the
orbit problem for `φ`.
-/

namespace Smallgroups.UsefulTheorems

open SemidirectProduct

variable {N N' H H' : Type*} [Group N] [Group N'] [Group H] [Group H']
  {φ ψ : H →* MulAut N} {φ' : H' →* MulAut N'}

/-! ### The master isomorphism constructor -/

/-- **Comparing two semidirect products.** Given isomorphisms `θ : N ≃* N'` and `σ : H ≃* H'`
intertwining the actions (`θ ∘ φ h = φ' (σ h) ∘ θ` for all `h`), the map `(n, h) ↦ (θ n, σ h)` is an
isomorphism `N ⋊[φ] H ≃* N' ⋊[φ'] H'`. -/
noncomputable def semidirectProductCongr (θ : N ≃* N') (σ : H ≃* H')
    (compat : ∀ h, θ.toMonoidHom.comp (φ h).toMonoidHom
      = (φ' (σ h)).toMonoidHom.comp θ.toMonoidHom) :
    SemidirectProduct N H φ ≃* SemidirectProduct N' H' φ' :=
  MulEquiv.ofBijective (SemidirectProduct.map θ.toMonoidHom σ.toMonoidHom compat) <| by
    constructor
    · intro x y hxy
      have hl := congrArg SemidirectProduct.left hxy
      have hr := congrArg SemidirectProduct.right hxy
      simp only [SemidirectProduct.map_left, SemidirectProduct.map_right,
        MulEquiv.coe_toMonoidHom, EmbeddingLike.apply_eq_iff_eq] at hl hr
      exact SemidirectProduct.ext hl hr
    · intro z
      refine ⟨⟨θ.symm z.left, σ.symm z.right⟩, SemidirectProduct.ext ?_ ?_⟩
      · simp
      · simp

/-! ### Corollaries: the orbit moves -/

/-- Equal actions give (canonically) isomorphic semidirect products. -/
noncomputable def semidirectProductCongr_eq (h : φ = ψ) :
    SemidirectProduct N H φ ≃* SemidirectProduct N H ψ :=
  semidirectProductCongr (MulEquiv.refl N) (MulEquiv.refl H) (by subst h; intro g; ext n; rfl)

/-- **Precomposing the action with an automorphism of `H`.** For `σ : H ≃* H`,
`N ⋊[φ ∘ σ] H ≃* N ⋊[φ] H`. -/
noncomputable def semidirectProductCongrAut (σ : H ≃* H) :
    SemidirectProduct N H (φ.comp σ.toMonoidHom) ≃* SemidirectProduct N H φ :=
  semidirectProductCongr (MulEquiv.refl N) σ (by intro h; ext n; rfl)

/-- **Conjugating the action by an automorphism of `N`.** For `θ : N ≃* N`, conjugating `φ` by `θ`
gives an isomorphic group: `N ⋊[φ] H ≃* N ⋊[θ φ θ⁻¹] H`. -/
noncomputable def semidirectProductCongrConj (θ : N ≃* N) :
    SemidirectProduct N H φ ≃* SemidirectProduct N H ((MulAut.conj θ).toMonoidHom.comp φ) :=
  semidirectProductCongr θ (MulEquiv.refl H) (by
    intro h; ext n
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.refl_apply]
    simp [MulAut.conj_apply])

/-! ### Faithfulness: the action is recovered from the group -/

/-- The action is recovered from the group structure: `φ h n` is the `N`-part of the conjugate
`inr h * inl n * (inr h)⁻¹`. -/
theorem conjAction_eq (h : H) (n : N) :
    φ h n = (inr h * inl n * inr h⁻¹ : SemidirectProduct N H φ).left := by
  rw [← SemidirectProduct.inl_aut]
  rfl

/-- **Faithfulness / the parametrisation is one-to-one.** An isomorphism `N ⋊[φ] H ≃* N ⋊[ψ] H`
fixing the canonical inclusions `inl` and `inr` forces the actions to agree. -/
theorem semidirectProduct_action_inj (e : SemidirectProduct N H φ ≃* SemidirectProduct N H ψ)
    (hl : ∀ n, e (inl n) = inl n) (hr : ∀ h, e (inr h) = inr h) : φ = ψ := by
  ext h n
  have key : (inl (φ h n) : SemidirectProduct N H ψ) = inl (ψ h n) := by
    have hcalc : e (inl (φ h n)) = (inl (ψ h n) : SemidirectProduct N H ψ) := by
      rw [SemidirectProduct.inl_aut, map_mul, map_mul, hr, hl, hr, ← SemidirectProduct.inl_aut]
    rwa [hl] at hcalc
  exact SemidirectProduct.inl_inj.mp key

end Smallgroups.UsefulTheorems
