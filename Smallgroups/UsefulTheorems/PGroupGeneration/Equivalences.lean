/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleGroup

/-!
# p-group generation: isomorphisms between cocycle groups

The pruning moves of the p-group generation machinery: three standard operations on a
normalized 2-cocycle `f : Q → Q → M` that do not change the isomorphism type of
`CocycleGroup f hf`.

* **Coboundary shift** (`CocycleGroup.coboundaryEquiv`): replacing `f` by
  `addCoboundary f d = f + ∂d` for any `d : Q → M` with `d 1 = 0` — this corresponds to
  changing the set-theoretic section in the reconstruction, so cohomologous cocycles give
  the *same* extension.
* **Base transport** (`CocycleGroup.congrRight`): precomposing with an isomorphism
  `α : Q' ≃* Q` of the base — this is the `Aut Q`-action responsible for merging
  descendants of `Q` that differ by an automorphism of `Q`.
* **Coefficient transport** (`CocycleGroup.congrLeft`): postcomposing with an additive
  isomorphism `σ : M ≃+ M'` — for `M = ZMod p` this is the `(ZMod p)ˣ`-rescaling action.

Together with `zeroEquivProd` (the zero cocycle yields the direct product), these are the
moves used to cut the cocycles produced by `cocycleGroup_reconstruction` down to the actual
isomorphism classes of order `p ^ (n + 1)`.  (Distinctness of the surviving classes is
proved separately, by isomorphism invariants, as everywhere else in this project.)
-/

namespace Smallgroups.UsefulTheorems

variable {Q : Type*} [Group Q] {M : Type*} [AddCommGroup M]

/-- The shift of `f` by the coboundary of `d : Q → M`. -/
def addCoboundary (f : Q → Q → M) (d : Q → M) : Q → Q → M :=
  fun a b => f a b + (d a + d b - d (a * b))

theorem IsCentralCocycle.addCoboundary {f : Q → Q → M} (hf : IsCentralCocycle f)
    (d : Q → M) (hd : d 1 = 0) :
    IsCentralCocycle (Smallgroups.UsefulTheorems.addCoboundary f d) := by
  constructor
  · intro a b c
    change f a b + (d a + d b - d (a * b)) + (f (a * b) c + (d (a * b) + d c - d (a * b * c)))
      = f b c + (d b + d c - d (b * c)) + (f a (b * c) + (d a + d (b * c) - d (a * (b * c))))
    rw [show f (a * b) c = f b c + f a (b * c) - f a b from
      eq_sub_of_add_eq' (hf.cocycle a b c), mul_assoc a b c]
    abel
  · intro a
    change f 1 a + (d 1 + d a - d (1 * a)) = 0
    rw [hf.one_left, hd, one_mul]
    abel
  · intro a
    change f a 1 + (d a + d 1 - d (a * 1)) = 0
    rw [hf.one_right, hd, mul_one]
    abel

/-- Cohomologous cocycles give isomorphic extensions: shifting `f` by a coboundary does not
change the cocycle group. -/
def CocycleGroup.coboundaryEquiv {f : Q → Q → M} (hf : IsCentralCocycle f)
    (d : Q → M) (hd : d 1 = 0) :
    CocycleGroup (addCoboundary f d) (hf.addCoboundary d hd) ≃* CocycleGroup f hf where
  toFun x := ⟨x.fst + d x.snd, x.snd⟩
  invFun x := ⟨x.fst - d x.snd, x.snd⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by
    ext
    · change x.fst + y.fst + (f x.snd y.snd
          + (d x.snd + d y.snd - d (x.snd * y.snd))) + d (x.snd * y.snd)
        = x.fst + d x.snd + (y.fst + d y.snd) + f x.snd y.snd
      abel
    · rfl

/-- Precomposing a cocycle with a group homomorphism preserves the cocycle property. -/
theorem IsCentralCocycle.comp {Q' : Type*} [Group Q'] {f : Q → Q → M}
    (hf : IsCentralCocycle f) (α : Q' →* Q) :
    IsCentralCocycle (fun a b => f (α a) (α b)) := by
  constructor
  · intro a b c
    show f (α a) (α b) + f (α (a * b)) (α c) = f (α b) (α c) + f (α a) (α (b * c))
    rw [map_mul, map_mul]
    exact hf.cocycle (α a) (α b) (α c)
  · intro a
    show f (α 1) (α a) = 0
    rw [map_one]
    exact hf.one_left (α a)
  · intro a
    show f (α a) (α 1) = 0
    rw [map_one]
    exact hf.one_right (α a)

/-- Transport of the base along `α : Q' ≃* Q`: the `Aut Q`-action on cocycles does not
change the isomorphism type of the extension. -/
def CocycleGroup.congrRight {Q' : Type*} [Group Q'] {f : Q → Q → M}
    (hf : IsCentralCocycle f) (α : Q' ≃* Q) :
    CocycleGroup (fun a b => f (α a) (α b)) (hf.comp α.toMonoidHom)
      ≃* CocycleGroup f hf where
  toFun x := ⟨x.fst, α x.snd⟩
  invFun x := ⟨x.fst, α.symm x.snd⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by
    ext
    · rfl
    · exact map_mul α x.snd y.snd

/-- Postcomposing a cocycle with an additive homomorphism preserves the cocycle
property. -/
theorem IsCentralCocycle.map {M' : Type*} [AddCommGroup M'] {f : Q → Q → M}
    (hf : IsCentralCocycle f) (σ : M →+ M') :
    IsCentralCocycle (fun a b => σ (f a b)) := by
  constructor
  · intro a b c
    show σ (f a b) + σ (f (a * b) c) = σ (f b c) + σ (f a (b * c))
    rw [← map_add, ← map_add, hf.cocycle]
  · intro a
    show σ (f 1 a) = 0
    rw [hf.one_left, map_zero]
  · intro a
    show σ (f a 1) = 0
    rw [hf.one_right, map_zero]

/-- Transport of the coefficients along `σ : M ≃+ M'`: rescaling the values of the cocycle
by an automorphism of the kernel does not change the isomorphism type. -/
def CocycleGroup.congrLeft {M' : Type*} [AddCommGroup M'] {f : Q → Q → M}
    (hf : IsCentralCocycle f) (σ : M ≃+ M') :
    CocycleGroup f hf ≃* CocycleGroup (fun a b => σ (f a b)) (hf.map σ.toAddMonoidHom) where
  toFun x := ⟨σ x.fst, x.snd⟩
  invFun x := ⟨σ.symm x.fst, x.snd⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by
    ext
    · change σ (x.fst + y.fst + f x.snd y.snd) = σ x.fst + σ y.fst + σ (f x.snd y.snd)
      rw [map_add, map_add]
    · rfl

/-- The zero cocycle yields the direct product `M × Q`. -/
def CocycleGroup.zeroEquivProd :
    CocycleGroup (fun _ _ : Q => (0 : M)) IsCentralCocycle.zero
      ≃* Multiplicative M × Q where
  toFun x := (Multiplicative.ofAdd x.fst, x.snd)
  invFun x := ⟨x.1.toAdd, x.2⟩
  left_inv x := by ext <;> simp
  right_inv x := by simp
  map_mul' x y := by
    ext
    · change Multiplicative.ofAdd (x.fst + y.fst + 0) = Multiplicative.ofAdd x.fst
        * Multiplicative.ofAdd y.fst
      rw [add_zero, ofAdd_add]
    · rfl

end Smallgroups.UsefulTheorems
