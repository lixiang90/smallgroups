/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.GAPClassification
import Smallgroups.UsefulTheorems.Order32Certificate.Alignment

/-!
# Classification of groups of order 32

The representatives here are the 51 kernel-checked central extensions produced by the
p-group generation certificate.  Their order agrees with GAP, but their definitions are
the cocycle-extension constructions rather than the imported PC presentations.
-/

namespace Smallgroups.Classifications.Order32

open Smallgroups.UsefulTheorems
open Smallgroups.UsefulTheorems.Order32Certificate

/-- The 51 central-extension representatives of order 32. -/
abbrev Rep : Fin 51 → Type := generatedFamily

/-- The generated central-extension family is complete and non-redundant. -/
theorem isClassif : IsClassif 32 Rep :=
  IsClassif.of_equivs smallGroup32_isClassif generatedFamilyGapEquiv

/-- Every group of order 32 is isomorphic to one of the generated representatives. -/
theorem classification {G : Type} [Group G] (h : Nat.card G = 32) :
    ∃ i, Nonempty (G ≃* Rep i) :=
  isClassif.complete G h

/-- The generated representatives are pairwise non-isomorphic. -/
theorem distinct {i j : Fin 51} (hij : i ≠ j) :
    ¬ Nonempty (Rep i ≃* Rep j) :=
  fun h => hij (isClassif.distinct i j h)

/-- There are exactly 51 isomorphism classes of groups of order 32. -/
theorem numIsoClasses_eq {k : ℕ} {rep : Fin k → Type} [∀ i, Group (rep i)]
    (h : IsClassif 32 rep) : k = 51 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order32
