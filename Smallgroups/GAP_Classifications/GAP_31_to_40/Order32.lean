/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.GAPClassification

/-!
# GAP-numbered classification of groups of order 32

Index `i : Fin 51` denotes exactly `SmallGroup(32, i + 1)`.
-/

namespace Smallgroups.GAP_Classifications.Order32

open Smallgroups.GAP Smallgroups.UsefulTheorems
open Smallgroups.UsefulTheorems.Order32Certificate

/-- The GAP-numbered representatives `SmallGroup(32,1..51)`. -/
abbrev gapRep : Fin 51 → Type := smallGroup32

/-- Every group of order 32 is isomorphic to a GAP representative. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 32) :
    ∃ i, Nonempty (G ≃* gapRep i) :=
  smallGroup32_isClassif.complete G h

/-- Different GAP indices give non-isomorphic groups. -/
theorem distinct {i j : Fin 51} (hij : i ≠ j) :
    ¬ Nonempty (gapRep i ≃* gapRep j) :=
  fun h => hij (smallGroup32_isClassif.distinct i j h)

/-- The GAP list is complete and non-redundant. -/
theorem isClassif : IsClassif 32 gapRep := smallGroup32_isClassif

/-- There are exactly 51 isomorphism classes of groups of order 32. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 32 rep) : k = 51 :=
  (isClassif.card_unique h).symm

end Smallgroups.GAP_Classifications.Order32
