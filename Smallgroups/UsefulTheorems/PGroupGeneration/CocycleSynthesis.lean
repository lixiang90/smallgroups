/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.GF2Certificate

/-! Linear combinations of checked cocycle columns remain cocycles. -/

namespace Smallgroups.UsefulTheorems.GF2Certificate

open scoped BigOperators

theorem IsCentralCocycle.linearCombination {Q : Type*} [Group Q]
    {k : ℕ} (f : Fin k → Q → Q → F2) (hf : ∀ i, IsCentralCocycle (f i))
    (c : Fin k → F2) :
    IsCentralCocycle (fun a b => ∑ i, c i * f i a b) := by
  constructor
  · intro a b d
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_add, ← mul_add, (hf i).cocycle]
  · intro a
    apply Finset.sum_eq_zero
    intro i _
    rw [(hf i).one_left, mul_zero]
  · intro a
    apply Finset.sum_eq_zero
    intro i _
    rw [(hf i).one_right, mul_zero]

namespace Order16Table

theorem isCentralCocycle_decodeTwo_synthesize (T : CertifiedGroupTable 16)
    {k : ℕ} (columns : Fin k → ℕ)
    (hcolumns : ∀ i, IsCentralCocycle (decodeTwo T (twoMask (columns i))))
    (c : Fin k → F2) : IsCentralCocycle (decodeTwo T (synthesizeTwo columns c)) := by
  have hform : decodeTwo T (synthesizeTwo columns c) =
      fun a b => ∑ i, c i * decodeTwo T (twoMask (columns i)) a b := by
    funext a b
    by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0 <;>
      simp [decodeTwo, synthesizeTwo, ha, hb]
  rw [hform]
  exact IsCentralCocycle.linearCombination _ hcolumns c

end Order16Table

end Smallgroups.UsefulTheorems.GF2Certificate
