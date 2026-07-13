/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order81
import Smallgroups.UsefulTheorems.Order81_CaseB

/-!
# Classification of groups of order 81

`81 = 3⁴`. There are exactly **fifteen** isomorphism classes of groups of order `81`:
five abelian and ten non-abelian.

**Abelian (five classes).** One for each partition of `4`, via the general
`ℤ/pᵃ`-abelian engine (`Smallgroups.UsefulTheorems.order81_abelian_reps`):
`ℤ/81`, `ℤ/27 × ℤ/3`, `ℤ/9 × ℤ/9`, `ℤ/9 × ℤ/3 × ℤ/3`, `ℤ/3 × ℤ/3 × ℤ/3 × ℤ/3`.

**Non-abelian (ten classes).** Every non-abelian group of order `81` has a normal
abelian subgroup of order `27`, of type `ℤ/9 × ℤ/3` or elementary abelian `(ℤ/3)³`,
with a non-trivial induced `ℤ/3`-action from conjugation by an outside element. The
ten classes arise as:
* the two "split" classes over an elementary abelian `(ℤ/3)³` kernel (the full Jordan
  block action, and a rank-`1` unipotent action giving the Heisenberg group `H₃ × ℤ/3`);
* five "split" classes over a `ℤ/9 × ℤ/3` kernel, classified by a full case-bash over
  the `27`-element parameter space of order-dividing-`3` automorphisms
  (`order81_c9c3_shear_rep`, `order81_c9c3_lift_rep`, `order81_c9c3_doubleShear_rep`,
  `order81_c9c3_sixShear_rep`, and `order81_semidirectP2P_prod_cyclic`, the last also
  reachable as a non-split rank-`1` extension over `(ℤ/3)³`);
* one class with an element of order `27` (`order81_c27_semidirect_rep`, `ℤ/27 ⋊ ℤ/3`),
  closed via cyclic-kernel cohomology triviality;
* two "non-split" classes over a `ℤ/9 × ℤ/3` kernel with no element of order `27`
  (`order81_c9_semidirect_c9_rep`, `ℤ/9 ⋊ ℤ/9`, and `order81_c9c3_nonSplit_rep`, the
  genuinely non-split six-shear extension), distinguished by whether the centralizer
  of an outside element has order `9` or `3`.

This file re-exports the bundled result
`Smallgroups.UsefulTheorems.order81_isClassif : IsClassif 81 order81_reps`, assembled
across `Smallgroups.UsefulTheorems.Order81` (the fifteen representatives, their orders,
and their pairwise distinctness) and `Smallgroups.UsefulTheorems.Order81_CaseB` (the
final exhaustiveness gap: every non-split, no-order-`27` extension over a `ℤ/9 × ℤ/3`
kernel is one of the two representatives above).
-/

namespace Smallgroups.Classifications.Order81

open Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order `81` is isomorphic to one of the
fifteen representatives. -/
theorem classification (G : Type) [Group G] (h : Nat.card G = 81) :
    ∃ n : Fin 15, Nonempty (G ≃* order81_reps n) :=
  order81_complete G h

/-- **(2) Distinctness.** The fifteen representatives are pairwise non-isomorphic. -/
theorem distinct : ∀ i j, Nonempty (order81_reps i ≃* order81_reps j) → i = j :=
  order81_isClassif.distinct

/-- **(3) Counting.** The fifteen representatives are a complete, non-redundant list
of representatives of the groups of order `81`. -/
theorem isClassif : IsClassif 81 order81_reps := order81_isClassif

/-- **The number of isomorphism classes of groups of order `81` is exactly `15`.** -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 81 rep) : k = 15 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order81
