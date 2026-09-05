/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticNormalForms4

/-!
# Separation of the seven four-dimensional normal forms

The number of zeros separates all but the two forms with eight zeros. Of those,
only the single-square form has identically zero polarization. Both properties
are invariant under linear isometry. The small representative computations below
are checked by the kernel on the sixteen vectors of each standard space.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

abbrev QuadraticFourV := QuadraticPlaneV × QuadraticPlaneV

/-- A computable pair of isometry invariants for the seven standard forms. -/
def quadraticFourProfile (Q : QuadraticMap F2 QuadraticFourV F2) : ℕ × Bool :=
  ((Finset.univ.filter (fun v => Q v = 0)).card,
    decide (∀ x y, Q (x + y) = Q x + Q y))

theorem quadraticFourProfile_equivalent {Q Q' : QuadraticMap F2 QuadraticFourV F2}
    (h : Q.Equivalent Q') : quadraticFourProfile Q = quadraticFourProfile Q' := by
  obtain ⟨e⟩ := h
  apply Prod.ext
  · change (Finset.univ.filter (fun v => Q v = 0)).card =
      (Finset.univ.filter (fun v => Q' v = 0)).card
    simpa only [Fintype.card_subtype] using Fintype.card_congr e.zeroFiberEquiv
  · have hiff : (∀ x y, Q (x + y) = Q x + Q y) ↔
        (∀ x y, Q' (x + y) = Q' x + Q' y) := by
      constructor
      · intro h x y
        obtain ⟨u, rfl⟩ := e.toLinearEquiv.surjective x
        obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective y
        change Q' (e u + e v) = Q' (e u) + Q' (e v)
        simpa only [← map_add e, e.map_app] using h u v
      · intro h x y
        simpa only [← map_add e, e.map_app] using h (e x) (e y)
    change decide (∀ x y, Q (x + y) = Q x + Q y) =
      decide (∀ x y, Q' (x + y) = Q' x + Q' y)
    simp only [hiff]

/-- The profile table is evaluated only on the seven standard forms. -/
theorem quadraticFourNormalForm_profiles : ∀ o : Fin 7,
    quadraticFourProfile (quadraticFourNormalForm o) =
      ![(16, true), (8, true), (12, false), (4, false),
        (8, false), (10, false), (6, false)] o := by
  decide +kernel

/-- Distinct entries of the seven-form list are not isometric. -/
theorem quadraticFourNormalForm_equivalent_iff (o p : Fin 7) :
    (quadraticFourNormalForm o).Equivalent (quadraticFourNormalForm p) ↔ o = p := by
  constructor
  · intro h
    have hp := quadraticFourProfile_equivalent h
    rw [quadraticFourNormalForm_profiles, quadraticFourNormalForm_profiles] at hp
    have hinj : Function.Injective
        (fun i : Fin 7 => ![(16, true), (8, true), (12, false), (4, false),
          (8, false), (10, false), (6, false)] i : Fin 7 → ℕ × Bool) := by
      decide +kernel
    exact hinj hp
  · rintro rfl
    exact ⟨QuadraticMap.IsometryEquiv.refl _⟩

end Smallgroups.UsefulTheorems.GF2Certificate
