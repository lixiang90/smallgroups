/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Smallgroups.UsefulTheorems.PGroupGeneration.CentralExtension

/-!
# p-group generation: central extensions from 2-cocycles

The second ingredient of the p-group generation machinery: given a group `Q` and an
additive commutative group `M` (in practice `M = ZMod p`), a **normalized 2-cocycle**
`f : Q → Q → M` (with respect to the trivial action of `Q` on `M`) produces a group
`CocycleGroup f hf` on the carrier `M × Q` with multiplication

  `(m₁, q₁) * (m₂, q₂) = (m₁ + m₂ + f q₁ q₂, q₁ * q₂)`.

This is a central extension `1 → M → CocycleGroup f hf → Q → 1`:

* `CocycleGroup.inl : Multiplicative M →* CocycleGroup f hf` embeds `M` centrally
  (`inl_mem_center`);
* `CocycleGroup.rightHom : CocycleGroup f hf →* Q` is the projection, surjective with
  kernel exactly `inl.range` (`ker_rightHom`);
* `CocycleGroup.card_eq` — the extension has order `|M| * |Q|`.

The converse — every central extension of `Q` by `C_p` arises this way — is proved in
`PGroupGeneration/Reconstruction.lean`, and together they turn the classification of groups
of order `p ^ (n + 1)` into the analysis of cocycles over the known groups of order `p ^ n`.
-/

namespace Smallgroups.UsefulTheorems

variable {Q : Type*} [Group Q] {M : Type*} [AddCommGroup M]

/-- A **normalized 2-cocycle** on `Q` with values in `M` (trivial action): the cocycle
identity together with two-sided normalization at `1`. -/
structure IsCentralCocycle (f : Q → Q → M) : Prop where
  cocycle : ∀ a b c : Q, f a b + f (a * b) c = f b c + f a (b * c)
  one_left : ∀ a : Q, f 1 a = 0
  one_right : ∀ a : Q, f a 1 = 0

/-- On finite groups with decidable coefficient equality, being a normalized central
2-cocycle is a computable predicate.  This is the entry point for exhaustive cocycle
enumeration in the p-group generation algorithm. -/
instance instDecidableIsCentralCocycle [Fintype Q] [DecidableEq M]
    (f : Q → Q → M) : Decidable (IsCentralCocycle f) :=
  decidable_of_iff'
    ((∀ a b c : Q, f a b + f (a * b) c = f b c + f a (b * c)) ∧
     (∀ a : Q, f 1 a = 0) ∧ (∀ a : Q, f a 1 = 0))
    ⟨fun h => ⟨h.cocycle, h.one_left, h.one_right⟩,
     fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- The zero cocycle (yielding the direct product `M × Q`). -/
theorem IsCentralCocycle.zero : IsCentralCocycle (fun _ _ : Q => (0 : M)) :=
  ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- On inverses, a normalized cocycle is symmetric: `f q⁻¹ q = f q q⁻¹`. -/
theorem IsCentralCocycle.inv_comm {f : Q → Q → M} (hf : IsCentralCocycle f) (q : Q) :
    f q⁻¹ q = f q q⁻¹ := by
  have h := hf.cocycle q⁻¹ q q⁻¹
  simpa [hf.one_left, hf.one_right] using h

/-- The central extension of `Q` by `M` determined by a normalized 2-cocycle `f`: the
carrier is `M × Q` with multiplication twisted by `f`. -/
@[ext]
structure CocycleGroup {Q : Type*} [Group Q] {M : Type*} [AddCommGroup M]
    (f : Q → Q → M) (hf : IsCentralCocycle f) where
  /-- The `M`-component. -/
  fst : M
  /-- The `Q`-component. -/
  snd : Q

namespace CocycleGroup

variable {f : Q → Q → M} {hf : IsCentralCocycle f}

instance : Mul (CocycleGroup f hf) :=
  ⟨fun x y => ⟨x.fst + y.fst + f x.snd y.snd, x.snd * y.snd⟩⟩

instance : One (CocycleGroup f hf) := ⟨⟨0, 1⟩⟩

instance : Inv (CocycleGroup f hf) :=
  ⟨fun x => ⟨-x.fst - f x.snd x.snd⁻¹, x.snd⁻¹⟩⟩

@[simp] theorem mul_fst (x y : CocycleGroup f hf) :
    (x * y).fst = x.fst + y.fst + f x.snd y.snd := rfl

@[simp] theorem mul_snd (x y : CocycleGroup f hf) : (x * y).snd = x.snd * y.snd := rfl

@[simp] theorem one_fst : (1 : CocycleGroup f hf).fst = 0 := rfl

@[simp] theorem one_snd : (1 : CocycleGroup f hf).snd = 1 := rfl

@[simp] theorem inv_fst (x : CocycleGroup f hf) :
    x⁻¹.fst = -x.fst - f x.snd x.snd⁻¹ := rfl

@[simp] theorem inv_snd (x : CocycleGroup f hf) : x⁻¹.snd = x.snd⁻¹ := rfl

instance : Group (CocycleGroup f hf) where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc x y z := by
    have h : f (x.snd * y.snd) z.snd
        = f y.snd z.snd + f x.snd (y.snd * z.snd) - f x.snd y.snd :=
      eq_sub_of_add_eq' (hf.cocycle x.snd y.snd z.snd)
    ext
    · simp only [mul_fst, mul_snd, h]
      abel
    · simp only [mul_snd, mul_assoc]
  one_mul x := by
    ext
    · simp [hf.one_left]
    · simp
  mul_one x := by
    ext
    · simp [hf.one_right]
    · simp
  inv_mul_cancel x := by
    ext
    · simp only [mul_fst, inv_fst, inv_snd, hf.inv_comm, one_fst]
      abel
    · simp

/-- The central embedding `M → CocycleGroup f hf`, `m ↦ (m, 1)`. -/
def inl : Multiplicative M →* CocycleGroup f hf where
  toFun m := ⟨m.toAdd, 1⟩
  map_one' := by ext <;> simp
  map_mul' m m' := by ext <;> simp [hf.one_left]

@[simp] theorem inl_fst (m : Multiplicative M) :
    (inl (hf := hf) m).fst = m.toAdd := rfl

@[simp] theorem inl_snd (m : Multiplicative M) : (inl (hf := hf) m).snd = 1 := rfl

theorem inl_injective : Function.Injective (inl (hf := hf)) := by
  intro m m' h
  have := congrArg fst h
  simpa using this

/-- The image of `M` is central. -/
theorem inl_mem_center (m : Multiplicative M) :
    inl (hf := hf) m ∈ Subgroup.center (CocycleGroup f hf) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext
  · simp [hf.one_left, hf.one_right, add_comm]
  · simp

/-- The projection `CocycleGroup f hf → Q`. -/
def rightHom : CocycleGroup f hf →* Q where
  toFun := snd
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem rightHom_apply (x : CocycleGroup f hf) :
    rightHom (hf := hf) x = x.snd := rfl

theorem rightHom_surjective : Function.Surjective (rightHom (hf := hf)) :=
  fun q => ⟨⟨0, q⟩, rfl⟩

@[simp] theorem rightHom_inl (m : Multiplicative M) :
    rightHom (hf := hf) (inl (hf := hf) m) = 1 := rfl

/-- The kernel of the projection is exactly the central copy of `M`. -/
theorem ker_rightHom : (rightHom (hf := hf)).ker = (inl (hf := hf)).range := by
  ext x
  constructor
  · intro hx
    have hx' : x.snd = 1 := hx
    exact ⟨Multiplicative.ofAdd x.fst, by ext <;> simp [hx'.symm]⟩
  · rintro ⟨m, rfl⟩
    exact rfl

/-- The central copy of `M` is a normal subgroup (being central). -/
instance : (inl (hf := hf)).range.Normal :=
  normal_of_le_center (by rintro x ⟨m, rfl⟩; exact inl_mem_center m)

/-- `CocycleGroup f hf` is in (set-theoretic) bijection with `M × Q`. -/
def toProd : CocycleGroup f hf ≃ M × Q where
  toFun x := (x.fst, x.snd)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instDecidableEq [DecidableEq M] [DecidableEq Q] :
    DecidableEq (CocycleGroup f hf) :=
  fun _ _ => decidable_of_iff' _ CocycleGroup.ext_iff

instance instFintype [Fintype M] [Fintype Q] [DecidableEq M] [DecidableEq Q] :
    Fintype (CocycleGroup f hf) :=
  Fintype.ofEquiv _ (toProd (hf := hf)).symm

instance [Finite M] [Finite Q] : Finite (CocycleGroup f hf) :=
  Finite.of_equiv _ (toProd (hf := hf)).symm

theorem card_eq : Nat.card (CocycleGroup f hf) = Nat.card M * Nat.card Q := by
  rw [Nat.card_congr (toProd (hf := hf)), Nat.card_prod]

/-- The quotient of the extension by the central copy of `M` recovers `Q`. -/
noncomputable def quotientRangeInlEquiv :
    (CocycleGroup f hf ⧸ (inl (hf := hf)).range) ≃* Q :=
  (QuotientGroup.quotientMulEquivOfEq ker_rightHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ rightHom_surjective)

end CocycleGroup

end Smallgroups.UsefulTheorems
