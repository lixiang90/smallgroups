/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.Equivalences
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Finite central cohomology for p-group generation

This file packages normalized one-cochains, normalized central two-cocycles, and
coboundaries as finite additive objects.  It deliberately separates the trusted Lean
checker from future external linear-algebra/orbit generators: generated candidates can
be checked by membership in these finite spaces and then turned into `CocycleGroup`s.
-/

namespace Smallgroups.UsefulTheorems

variable (Q : Type*) [Group Q] (M : Type*) [AddCommGroup M]

/-- Normalized one-cochains `d : Q → M`, satisfying `d 1 = 0`. -/
def normalizedCochainsOne : AddSubgroup (Q → M) where
  carrier := {d | d 1 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro d e hd he
    change d 1 = 0 at hd
    change e 1 = 0 at he
    change d 1 + e 1 = 0
    simp [hd, he]
  neg_mem' := by
    intro d hd
    change d 1 = 0 at hd
    change -d 1 = 0
    simp [hd]

/-- Normalized central two-cocycles, as an additive subgroup of all two-cochains. -/
def centralCocycles : AddSubgroup (Q → Q → M) where
  carrier := {f | IsCentralCocycle f}
  zero_mem' := IsCentralCocycle.zero
  add_mem' := by
    intro f g hf hg
    constructor
    · intro a b c
      have hf' := hf.cocycle a b c
      have hg' := hg.cocycle a b c
      dsimp
      calc
        f a b + g a b + (f (a * b) c + g (a * b) c) =
            (f a b + f (a * b) c) + (g a b + g (a * b) c) := by abel
        _ = (f b c + f a (b * c)) + (g b c + g a (b * c)) := by rw [hf', hg']
        _ = f b c + g b c + (f a (b * c) + g a (b * c)) := by abel
    · intro a
      simp [hf.one_left, hg.one_left]
    · intro a
      simp [hf.one_right, hg.one_right]
  neg_mem' := by
    intro f hf
    constructor
    · intro a b c
      have h := congrArg Neg.neg (hf.cocycle a b c)
      dsimp
      calc
        -f a b + -f (a * b) c = -(f a b + f (a * b) c) := by abel
        _ = -(f b c + f a (b * c)) := h
        _ = -f b c + -f a (b * c) := by abel
    · intro a
      simp [hf.one_left]
    · intro a
      simp [hf.one_right]

/-- The (inhomogeneous, trivial-action) coboundary of a one-cochain. -/
def centralCoboundary (d : Q → M) : Q → Q → M :=
  fun a b => d a + d b - d (a * b)

theorem isCentralCocycle_centralCoboundary (d : Q → M) (hd : d 1 = 0) :
    IsCentralCocycle (centralCoboundary Q M d) := by
  constructor
  · intro a b c
    simp only [centralCoboundary, mul_assoc]
    abel
  · intro a
    simp [centralCoboundary, hd]
  · intro a
    simp [centralCoboundary, hd]

/-- The additive coboundary map from normalized one-cochains to central two-cocycles. -/
def centralCoboundaryHom : normalizedCochainsOne Q M →+ centralCocycles Q M where
  toFun d := ⟨centralCoboundary Q M d, isCentralCocycle_centralCoboundary Q M d d.2⟩
  map_zero' := by
    ext a b
    simp [centralCoboundary]
  map_add' d e := by
    ext a b
    simp [centralCoboundary]
    abel

/-- The subgroup of normalized two-coboundaries. -/
def centralCoboundaries : AddSubgroup (centralCocycles Q M) :=
  (centralCoboundaryHom Q M).range

instance instFintypeNormalizedCochainsOne [Fintype Q] [DecidableEq Q]
    [DecidableEq M] [Fintype M] :
    Fintype (normalizedCochainsOne Q M) := by
  letI : DecidablePred (fun d : Q → M => d ∈ normalizedCochainsOne Q M) := fun d => by
    change Decidable (d 1 = 0)
    infer_instance
  exact Subtype.fintype _

instance instFintypeCentralCocycles [Fintype Q] [DecidableEq Q]
    [DecidableEq M] [Fintype M] :
    Fintype (centralCocycles Q M) := by
  letI : DecidablePred (fun f : Q → Q → M => f ∈ centralCocycles Q M) := fun f => by
    change Decidable (IsCentralCocycle f)
    infer_instance
  exact Subtype.fintype _

/-- Exhaustive finite list of normalized one-cochains. -/
def normalizedCochainFinset [Fintype Q] [DecidableEq Q] [DecidableEq M] [Fintype M] :
    Finset (normalizedCochainsOne Q M) :=
  Finset.univ

/-- Exhaustive finite list of normalized central two-cocycles. -/
def centralCocycleFinset [Fintype Q] [DecidableEq Q] [DecidableEq M] [Fintype M] :
    Finset (centralCocycles Q M) :=
  Finset.univ

/-- Exhaustive finite list of normalized two-coboundaries. -/
def centralCoboundaryFinset [Fintype Q] [DecidableEq Q] [Fintype M] [DecidableEq M] :
    Finset (centralCocycles Q M) :=
  (normalizedCochainFinset Q M).image (centralCoboundaryHom Q M)

theorem mem_centralCocycleFinset [Fintype Q] [DecidableEq Q]
    [DecidableEq M] [Fintype M]
    (f : Q → Q → M) (hf : IsCentralCocycle f) :
    (⟨f, hf⟩ : centralCocycles Q M) ∈ centralCocycleFinset Q M := by
  simp [centralCocycleFinset]

theorem mem_centralCoboundaryFinset [Fintype Q] [DecidableEq Q]
    [Fintype M] [DecidableEq M] (d : Q → M) (hd : d 1 = 0) :
    (⟨centralCoboundary Q M d, isCentralCocycle_centralCoboundary Q M d hd⟩ :
      centralCocycles Q M) ∈ centralCoboundaryFinset Q M := by
  rw [centralCoboundaryFinset, Finset.mem_image]
  refine ⟨⟨d, hd⟩, ?_, ?_⟩
  · exact Finset.mem_univ _
  · rfl

/-! A small executable regression test: for the trivial action of `C₂` on `𝔽₂`,
there are two normalized central cocycles and one normalized coboundary. -/

theorem centralCocycleFinset_card_c2_zmod2 :
    (centralCocycleFinset (Multiplicative (ZMod 2)) (ZMod 2)).card = 2 := by
  decide +kernel

theorem centralCoboundaryFinset_card_c2_zmod2 :
    (centralCoboundaryFinset (Multiplicative (ZMod 2)) (ZMod 2)).card = 1 := by
  decide +kernel

/-! ## Linear-algebra presentation

For field coefficients (in particular `ZMod 2`), the same objects are exposed as
submodules.  This is the scalable interface: a generator can row-reduce the linear
cocycle equations externally, while Lean checks each basis vector against membership
in `centralCocycleSubmodule` and checks the quotient by the range below. -/

section Linear

variable (R : Type*) [CommRing R]

/-- Normalized one-cochains as an `R`-submodule. -/
def normalizedCochainSubmodule : Submodule R (Q → R) where
  carrier := {d | d 1 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro d e hd he
    change d 1 = 0 at hd
    change e 1 = 0 at he
    change d 1 + e 1 = 0
    simp [hd, he]
  smul_mem' := by
    intro r d hd
    change d 1 = 0 at hd
    change r • d 1 = 0
    simp [hd]

/-- Central normalized two-cocycles as the kernel-like solution submodule of the
homogeneous cocycle equations. -/
def centralCocycleSubmodule : Submodule R (Q → Q → R) where
  carrier := {f | IsCentralCocycle f}
  zero_mem' := IsCentralCocycle.zero
  add_mem' := (centralCocycles Q R).add_mem
  smul_mem' := by
    intro r f hf
    constructor
    · intro a b c
      change r * f a b + r * f (a * b) c = r * f b c + r * f a (b * c)
      rw [← mul_add, hf.cocycle, mul_add]
    · intro a
      change r * f 1 a = 0
      simp [hf.one_left]
    · intro a
      change r * f a 1 = 0
      simp [hf.one_right]

/-- The coboundary operator as an `R`-linear map. -/
def centralCoboundaryLinearMap :
    normalizedCochainSubmodule Q R →ₗ[R] centralCocycleSubmodule Q R where
  toFun d :=
    ⟨centralCoboundary Q R d, isCentralCocycle_centralCoboundary Q R d d.2⟩
  map_add' d e := by
    ext a b
    simp [centralCoboundary]
    ring
  map_smul' r d := by
    ext a b
    simp [centralCoboundary]
    ring

/-- The submodule of two-coboundaries. -/
def centralCoboundarySubmodule : Submodule R (centralCocycleSubmodule Q R) :=
  LinearMap.range (centralCoboundaryLinearMap Q R)

/-- The second cohomology module for the trivial action, `H²(Q,R) = Z²/B²`. -/
abbrev secondCentralCohomology :=
  ↥(centralCocycleSubmodule Q R) ⧸ centralCoboundarySubmodule Q R

end Linear

end Smallgroups.UsefulTheorems
