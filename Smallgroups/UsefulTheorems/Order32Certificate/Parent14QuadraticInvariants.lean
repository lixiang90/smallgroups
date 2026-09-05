/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticInvariants
import Smallgroups.UsefulTheorems.Order32Certificate.Parent14QuadraticBasics

/-! # Polar rank and radical square for Parent 14 -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

/-- The radical of the commutator pairing of a Parent 14 extension. -/
def parent14PolarRadical (c : Fin 10 → F2) : Submodule F2 Parent14V :=
  (parent14Quadratic c).polarBilin.ker

/-- The rank of the commutator pairing, computed from its kernel dimension. -/
noncomputable def parent14PolarRank (c : Fin 10 → F2) : ℕ :=
  4 - Module.finrank F2 (parent14PolarRadical c)

/-- The square function on central base vectors is a linear functional. -/
def parent14RadicalSquare (c : Fin 10 → F2) : parent14PolarRadical c →ₗ[F2] F2 :=
  quadraticPolarKernelRestriction (parent14Quadratic c)

/-- The commutator rank is invariant under linear changes of Parent 14 coordinates. -/
theorem parent14PolarRank_eq_of_equivalent {c d : Fin 10 → F2}
    (h : (parent14Quadratic c).Equivalent (parent14Quadratic d)) :
    parent14PolarRank c = parent14PolarRank d := by
  unfold parent14PolarRank parent14PolarRadical
  rw [h.finrank_ker_polarBilin_eq]

/-- The quadratic radical dimension is a second invariant, distinct from polar rank. -/
theorem parent14QuadraticRadical_finrank_eq_of_equivalent {c d : Fin 10 → F2}
    (h : (parent14Quadratic c).Equivalent (parent14Quadratic d)) :
    Module.finrank F2 (parent14Quadratic c).radical =
      Module.finrank F2 (parent14Quadratic d).radical :=
  h.rank_radical_eq

end Smallgroups.UsefulTheorems.Order32Certificate
