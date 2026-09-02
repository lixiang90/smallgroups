/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Basic

/-!
# A strong finite-group isomorphism invariant

For every element we record its power pattern, centralizer size, and numbers of square
and fourth roots.  The multiset of these local records is inexpensive on groups of order
32 but strong enough to separate all 51 GAP representatives.  The definitions are fully
computable; the theorems below establish invariance without trusting any external
classification program.
-/

namespace Smallgroups.UsefulTheorems

/-- Exponents used to encode the order pattern of an element of a group of order 32. -/
def order32PowerExponent : Fin 6 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32

/-- A six-bit encoding of which standard powers of `x` are one. -/
def order32PowerCode {G : Type*} [Group G] [DecidableEq G] (x : G) : ℕ :=
  ∑ i : Fin 6, if x ^ order32PowerExponent i = 1 then 2 ^ i.val else 0

/-- Number of elements commuting with `x`. -/
def elementCentralizerCard (G : Type*) [Group G] [Fintype G] [DecidableEq G] (x : G) : ℕ :=
  Fintype.card {y : G // y * x = x * y}

/-- Number of `n`th roots of `x`. -/
def elementRootCard (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (n : ℕ) (x : G) : ℕ :=
  Fintype.card {y : G // y ^ n = x}

/-- Per-element data used by the order-32 distinctness certificate. -/
abbrev Order32LocalFeature := ℕ × ℕ × ℕ × ℕ

def order32LocalFeature (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (x : G) : Order32LocalFeature :=
  (order32PowerCode x, elementCentralizerCard G x,
    elementRootCard G 2 x, elementRootCard G 4 x)

/-- The unordered collection of local features, with multiplicity. -/
def order32LocalProfile (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Multiset Order32LocalFeature :=
  (Finset.univ.val.map (order32LocalFeature G))

theorem order32PowerCode_map {G H : Type*} [Group G] [Group H]
    [DecidableEq G] [DecidableEq H] (e : G ≃* H) (x : G) :
    order32PowerCode (e x) = order32PowerCode x := by
  unfold order32PowerCode
  apply Finset.sum_congr rfl
  intro i _
  apply if_congr
  · constructor
    · intro h
      apply e.injective
      simpa using h
    · intro h
      rw [← map_pow, h, map_one]
  · rfl
  · rfl

theorem elementCentralizerCard_map {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (e : G ≃* H) (x : G) :
    elementCentralizerCard H (e x) = elementCentralizerCard G x := by
  symm
  apply Fintype.card_congr
  exact
    { toFun := fun y => ⟨e y.1, by simpa using congrArg e y.2⟩
      invFun := fun y => ⟨e.symm y.1, by
        simpa using congrArg e.symm y.2⟩
      left_inv := fun y => by ext; simp
      right_inv := fun y => by ext; simp }

theorem elementRootCard_map {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (e : G ≃* H) (n : ℕ) (x : G) :
    elementRootCard H n (e x) = elementRootCard G n x := by
  symm
  apply Fintype.card_congr
  exact
    { toFun := fun y => ⟨e y.1, by simpa using congrArg e y.2⟩
      invFun := fun y => ⟨e.symm y.1, by
        simpa using congrArg e.symm y.2⟩
      left_inv := fun y => by ext; simp
      right_inv := fun y => by ext; simp }

theorem order32LocalFeature_map {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (e : G ≃* H) (x : G) :
    order32LocalFeature H (e x) = order32LocalFeature G x := by
  simp only [order32LocalFeature, order32PowerCode_map e x,
    elementCentralizerCard_map e x, elementRootCard_map e 2 x,
    elementRootCard_map e 4 x]

/-- The local profile is transported exactly by every group isomorphism. -/
theorem order32LocalProfile_eq_of_mulEquiv {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (e : G ≃* H) : order32LocalProfile G = order32LocalProfile H := by
  unfold order32LocalProfile
  rw [← Multiset.map_univ_val_equiv e.toEquiv, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro x _
  exact (order32LocalFeature_map e x).symm

end Smallgroups.UsefulTheorems
