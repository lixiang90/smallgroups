/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PrimeOrderClassification
import Smallgroups.UsefulTheorems.Counting

/-!
# Classification of groups of order 1

There is exactly one group of order `1` up to isomorphism: the trivial group, which we represent
by `CyclicRep 1 = Multiplicative (ZMod 1)`.

* `classification` — (1) exhaustiveness: every group of order `1` is isomorphic to the trivial
  group.
* `distinct` — (2) distinctness: vacuous, as there is a single class.
* `isClassif` / `numIsoClasses_eq` — (3) counting: there is exactly one isomorphism class, proved
  from exhaustiveness and distinctness.
-/

namespace Smallgroups.Classifications.Order1

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- The unique isomorphism class of groups of order `1`: the trivial group. -/
abbrev Rep : Type := CyclicRep 1

/-- The representative has order `1`. -/
theorem card_Rep : Nat.card Rep = 1 := card_cyclicRep one_ne_zero

/-- **(1) Exhaustiveness.** Every group of order `1` is isomorphic to the trivial group. -/
theorem classification (h : Nat.card G = 1) : Nonempty (G ≃* Rep) := by
  haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h).1
  exact cyclicRep_classification one_ne_zero h

/-- A group of order `1` is (trivially) cyclic. -/
theorem isCyclic_of_card (h : Nat.card G = 1) : IsCyclic G := by
  haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h).1
  infer_instance

/-- **(2) Distinctness.** With a single class there are no two distinct representatives, so the
distinctness statement holds vacuously. -/
theorem distinct {i j : Fin 1} (hij : i ≠ j) :
    ¬ Nonempty (singleReps Rep i ≃* singleReps Rep j) :=
  singleReps_distinct Rep hij

/-- Any two groups of order `1` are isomorphic. -/
theorem unique {H : Type*} [Group H] (hG : Nat.card G = 1) (hH : Nat.card H = 1) :
    Nonempty (G ≃* H) :=
  ⟨(classification hG).some.trans (classification (G := H) hH).some.symm⟩

/-- **(3) Counting.** The one-element list `[trivial group]` is a complete, non-redundant list of
representatives of the groups of order `1` — assembled from exhaustiveness (`classification`) and
the (vacuous) distinctness. -/
theorem isClassif : IsClassif 1 (rep1 Rep) :=
  isClassif_one _ card_Rep (fun _ _ hG => classification hG)

/-- **The number of isomorphism classes of groups of order `1` is exactly `1`:** any complete list
of pairwise non-isomorphic representatives has length `1`. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 1 rep) : k = 1 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order1
