/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order72.H8xP9

/-!
# Groups of order 72: conjugacy classification of small-order automorphisms of `C3 × C3`

For the remaining Sylow-`3`-normal cells `E9 ⋊ H` (`H` one of the order-`8` groups
`H2 = C4 × C2`, `E8 = (C2)³`, `D4`, `Q8`) we classify homomorphisms
`H → MulAut (ElemAbelianRep 3) ≅ GL(2,3)` up to `Aut H × GL(2,3)`-conjugacy.  The engine
behind all four cells is the conjugacy classification of low-order elements of `GL(2,3)`
proved here by enumerating the `9 × 9` possible generator-image pairs:

* `order72_E9_sq_cases`: an involution of `GL(2,3)` is `1`, `-I`
  (`order72_E9_negAut`), or conjugate to the standard reflection
  `order72_E9_reflectAut` (the `12` involutions with eigenvalues `1, -1` form a single
  conjugacy class; explicit conjugators are given for each of the `11` nonstandard
  codes);
* `order72_E9_pow4_cases`: an element of order dividing `4` additionally may be
  conjugate to the standard order-`4` element `order72_E9_order4Aut` (all six order-`4`
  elements are conjugate);
* `order72_E9_reflect_centralizer_sq_cases`: an involution commuting with the standard
  reflection is one of `1`, `-I`, the reflection itself, or `diag(1,-1)`;
* `order72_E9_order4_centralizer_sq_cases`: an involution commuting with the standard
  order-`4` element is `1` or `-I`.

The `9 × 9` enumeration pairs each generator value with a code via
`order72_E9_code_of_gen_values`; matching a code against a concrete automorphism `X` is a
single `decide`, so non-matching alternatives fail silently.  Every remaining case is
discharged by evaluating the appropriate iterate (`order72_E9_pow_eq_homOfValuesFun_iter`)
or commutation relation on the pinned values and finishing with a single `decide` on the
conjunction of the constraints.
-/

namespace Smallgroups.UsefulTheorems

open P3Group

/-- `-I` is central in `GL(2,3)` (it acts by squaring on the exponent-`3` group). -/
theorem order72_E9_negAut_apply (x : ElemAbelianRep 3) : order72_E9_negAut x = x ^ 2 := by
  revert x
  decide

theorem order72_E9_negAut_central (g : MulAut (ElemAbelianRep 3)) :
    Commute g order72_E9_negAut := by
  change g * order72_E9_negAut = order72_E9_negAut * g
  apply DFunLike.ext
  intro x
  change g (order72_E9_negAut x) = order72_E9_negAut (g x)
  rw [order72_E9_negAut_apply, order72_E9_negAut_apply, map_pow]

/-- Conjugation fixes `-I`. -/
theorem order72_E9_conj_negAut (θ : MulAut (ElemAbelianRep 3)) :
    (MulAut.conj θ) order72_E9_negAut = order72_E9_negAut := by
  rw [MulAut.conj_apply, (order72_E9_negAut_central θ).eq, mul_assoc, mul_inv_cancel,
    mul_one]

/-- The standard order-`4` element squares to `-I`. -/
theorem order72_E9_order4Aut_sq : order72_E9_order4Aut ^ 2 = order72_E9_negAut := by
  apply order72_E9_aut_ext <;> decide

/-! ### The code of a pinned automorphism, and case lemmas. -/

/-- The code of an automorphism pinned by its two generator values. -/
theorem order72_E9_code_of_gen_values {f : MulAut (ElemAbelianRep 3)}
    {x y : ElemAbelianRep 3} {X : MulAut (ElemAbelianRep 3)}
    (h1 : f order72_E9_g1 = x) (h2 : f order72_E9_g2 = y)
    (hc : (order72_E9_coord x, order72_E9_coord y) = order72_E9_autCode X) :
    order72_E9_autCode f = order72_E9_autCode X := by
  change (order72_E9_coord (f order72_E9_g1), order72_E9_coord (f order72_E9_g2)) = _
  rw [h1, h2]
  exact hc

/-- An automorphism with the identity's code is the identity. -/
theorem order72_E9_eq_one_of_code {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode 1) : f = 1 :=
  order72_E9_autCode_injective hφ

/-- An automorphism with `-I`'s code is `-I`. -/
theorem order72_E9_eq_neg_of_code {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode order72_E9_negAut) :
    f = order72_E9_negAut :=
  order72_E9_autCode_injective hφ

/-- An automorphism with the standard reflection's code is the standard reflection. -/
theorem order72_E9_eq_reflect_of_code {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode order72_E9_reflectAut) :
    f = order72_E9_reflectAut :=
  order72_E9_autCode_injective hφ

/-- An automorphism with `diag(1,-1)`'s code is `diag(1,-1)`. -/
theorem order72_E9_eq_scaleSecond2_of_code {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode order72_E9_scaleSecond2) :
    f = order72_E9_scaleSecond2 :=
  order72_E9_autCode_injective hφ

/-- An automorphism with the standard order-`4` element's code is that element. -/
theorem order72_E9_eq_order4_of_code {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode order72_E9_order4Aut) :
    f = order72_E9_order4Aut :=
  order72_E9_autCode_injective hφ

/-- An automorphism with the code of `order72_E9_order4Aut ^ 3` is `order72_E9_order4Aut ^ 3`. -/
theorem order72_E9_eq_order4_pow3_of_code {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode (order72_E9_order4Aut ^ 3)) :
    f = order72_E9_order4Aut ^ 3 :=
  order72_E9_autCode_injective hφ

/-- A pinned order-`4`-class automorphism is conjugate to the standard order-`4` element. -/
theorem order72_E9_conj_order4_of_code_pow3 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode (order72_E9_order4Aut ^ 3)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_order4Aut :=
  ⟨order72_E9_scaleFirst2.symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned involution of code `2101` is conjugate to the standard reflection. -/
theorem order72_E9_conj_reflect_of_code_2101 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode ((MulAut.conj order72_E9_shearLower)
      order72_E9_reflectAut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut :=
  ⟨order72_E9_shearLower.symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned involution of code `2201` is conjugate to the standard reflection. -/
theorem order72_E9_conj_reflect_of_code_2201 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode ((MulAut.conj (order72_E9_shearLower ^ 2))
      order72_E9_reflectAut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut :=
  ⟨(order72_E9_shearLower ^ 2).symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned involution of code `1002` is conjugate to the standard reflection. -/
theorem order72_E9_conj_reflect_of_code_1002 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode ((MulAut.conj order72_E9_swap)
      order72_E9_reflectAut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut :=
  ⟨order72_E9_swap, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned involution of code `1102` is conjugate to the standard reflection. -/
theorem order72_E9_conj_reflect_of_code_1102 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode
    ((MulAut.conj (order72_E9_shearLower.symm * order72_E9_swap))
      order72_E9_reflectAut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut :=
  ⟨order72_E9_shearLower.trans order72_E9_swap, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned involution of code `1202` is conjugate to the standard reflection. -/
theorem order72_E9_conj_reflect_of_code_1202 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode
    ((MulAut.conj (order72_E9_shearLower * order72_E9_swap))
      order72_E9_reflectAut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut :=
  ⟨order72_E9_shearLower.symm.trans order72_E9_swap, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned involution of code `0110` is conjugate to the standard reflection. -/
theorem order72_E9_conj_reflect_of_code_0110 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode ((MulAut.conj order72_E9_swapReflectBasis)
      order72_E9_reflectAut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut :=
  ⟨order72_E9_swapReflectBasis.symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned involution of code `2011` is conjugate to the standard reflection. -/
theorem order72_E9_conj_reflect_of_code_2011 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode
    ((MulAut.conj (order72_E9_shearLower * order72_E9_swapReflectBasis))
      order72_E9_reflectAut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut :=
  ⟨order72_E9_shearLower.symm.trans order72_E9_swapReflectBasis.symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned involution of code `1012` is conjugate to the standard reflection. -/
theorem order72_E9_conj_reflect_of_code_1012 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode
    ((MulAut.conj ((order72_E9_shearLower ^ 2) * order72_E9_swapReflectBasis))
      order72_E9_reflectAut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut :=
  ⟨(order72_E9_shearLower ^ 2).symm.trans order72_E9_swapReflectBasis.symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned involution of code `0220` is conjugate to the standard reflection. -/
theorem order72_E9_conj_reflect_of_code_0220 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode ((MulAut.conj order72_E9_negSwapReflectBasis)
      order72_E9_reflectAut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut :=
  ⟨order72_E9_negSwapReflectBasis.symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned involution of code `2021` is conjugate to the standard reflection. -/
theorem order72_E9_conj_reflect_of_code_2021 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode ((MulAut.conj order72_E9_shearPlus)
      order72_E9_reflectAut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut :=
  ⟨order72_E9_shearPlus.symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned involution of code `1022` is conjugate to the standard reflection. -/
theorem order72_E9_conj_reflect_of_code_1022 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode
    ((MulAut.conj (order72_E9_shearPlus.symm * order72_E9_swap))
      order72_E9_reflectAut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut :=
  ⟨order72_E9_shearPlus.trans order72_E9_swap, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned order-`4`-class automorphism of code `1112` is conjugate to the
standard order-`4` element. -/
theorem order72_E9_conj_order4_of_code_1112 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode ((MulAut.conj order72_E9_shearPlus)
      order72_E9_order4Aut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_order4Aut :=
  ⟨order72_E9_shearPlus.symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned order-`4`-class automorphism of code `2221` is conjugate to the
standard order-`4` element. -/
theorem order72_E9_conj_order4_of_code_2221 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode
    ((MulAut.conj ((order72_E9_shearPlus ^ 2).trans order72_E9_scaleSecond2))
      order72_E9_order4Aut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_order4Aut :=
  ⟨((order72_E9_shearPlus ^ 2).trans order72_E9_scaleSecond2).symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned order-`4`-class automorphism of code `1222` is conjugate to the
standard order-`4` element. -/
theorem order72_E9_conj_order4_of_code_1222 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode
    ((MulAut.conj (order72_E9_shearPlus.trans order72_E9_scaleSecond2))
      order72_E9_order4Aut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_order4Aut :=
  ⟨(order72_E9_shearPlus.trans order72_E9_scaleSecond2).symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-- A pinned order-`4`-class automorphism of code `2111` is conjugate to the
standard order-`4` element. -/
theorem order72_E9_conj_order4_of_code_2111 {f : MulAut (ElemAbelianRep 3)}
    (hφ : order72_E9_autCode f = order72_E9_autCode ((MulAut.conj (order72_E9_shearPlus ^ 2))
      order72_E9_order4Aut)) :
    ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_order4Aut :=
  ⟨(order72_E9_shearPlus ^ 2).symm, by
    rw [order72_E9_autCode_injective hφ]
    apply order72_E9_autCode_injective
    decide⟩


/-! ### Involutions of `GL(2,3)`. -/

/-- **Involutions of `GL(2,3)`**: every `f` with `f ^ 2 = 1` is the identity, `-I`, or
conjugate to the standard reflection.  The `14` element codes of order dividing `2` are
accepted directly (with explicit conjugators for the `11` noncentral involutions); each
of the other `67` generator-image pairs contradicts `f ^ 2 = 1`. -/
theorem order72_E9_sq_cases (f : MulAut (ElemAbelianRep 3)) (hf : f ^ 2 = 1) :
    f = 1 ∨ f = order72_E9_negAut ∨
      ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut := by
  rcases order72_E9_total_cases (f order72_E9_g1) with h1 | h1 | h1 | h1 | h1 | h1 | h1 |
    h1 | h1 <;>
    rcases order72_E9_total_cases (f order72_E9_g2) with h2 | h2 | h2 | h2 | h2 | h2 | h2 |
      h2 | h2 <;>
    first
    | exact Or.inl (order72_E9_eq_one_of_code (order72_E9_code_of_gen_values h1 h2 (by decide)))
    | exact Or.inr (Or.inl (order72_E9_eq_neg_of_code
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (⟨1, by rw [order72_E9_eq_reflect_of_code
    (order72_E9_code_of_gen_values h1 h2 (by decide))]; rfl⟩))
    | exact Or.inr (Or.inr (order72_E9_conj_reflect_of_code_2101
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (order72_E9_conj_reflect_of_code_2201
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (order72_E9_conj_reflect_of_code_1002
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (order72_E9_conj_reflect_of_code_1102
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (order72_E9_conj_reflect_of_code_1202
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (order72_E9_conj_reflect_of_code_0110
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (order72_E9_conj_reflect_of_code_2011
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (order72_E9_conj_reflect_of_code_1012
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (order72_E9_conj_reflect_of_code_0220
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (order72_E9_conj_reflect_of_code_2021
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (order72_E9_conj_reflect_of_code_1022
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exfalso
      have hg1 : (f ^ 2) order72_E9_g1 = order72_E9_g1 := by rw [hf]; rfl
      have hg2 : (f ^ 2) order72_E9_g2 = order72_E9_g2 := by rw [hf]; rfl
      rw [order72_E9_pow_eq_homOfValuesFun_iter f h1 h2 2 order72_E9_g1] at hg1
      rw [order72_E9_pow_eq_homOfValuesFun_iter f h1 h2 2 order72_E9_g2] at hg2
      have hpair : _ ∧ _ := ⟨hg1, hg2⟩
      exact absurd hpair (by decide)

/-! ### Elements of order dividing `4`. -/

/-- **Elements of `GL(2,3)` of order dividing `4`**: every `f` with `f ^ 4 = 1` is the
identity, `-I`, conjugate to the standard reflection, or conjugate to the standard
order-`4` element.  The `20` element codes of order dividing `4` are accepted directly;
each remaining generator-image pair contradicts `f ^ 4 = 1`. -/
theorem order72_E9_pow4_cases (f : MulAut (ElemAbelianRep 3)) (hf : f ^ 4 = 1) :
    f = 1 ∨ f = order72_E9_negAut ∨
      (∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_reflectAut) ∨
        ∃ θ : MulAut (ElemAbelianRep 3), (MulAut.conj θ) f = order72_E9_order4Aut := by
  rcases order72_E9_total_cases (f order72_E9_g1) with h1 | h1 | h1 | h1 | h1 | h1 | h1 |
    h1 | h1 <;>
    rcases order72_E9_total_cases (f order72_E9_g2) with h2 | h2 | h2 | h2 | h2 | h2 | h2 |
      h2 | h2 <;>
    first
    | exact Or.inl (order72_E9_eq_one_of_code (order72_E9_code_of_gen_values h1 h2 (by decide)))
    | exact Or.inr (Or.inl (order72_E9_eq_neg_of_code
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_conj_reflect_of_code_2101
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_conj_reflect_of_code_2201
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_conj_reflect_of_code_1002
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_conj_reflect_of_code_1102
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_conj_reflect_of_code_1202
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_conj_reflect_of_code_0110
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_conj_reflect_of_code_2011
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_conj_reflect_of_code_1012
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_conj_reflect_of_code_0220
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_conj_reflect_of_code_2021
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_conj_reflect_of_code_1022
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (⟨1, by rw [order72_E9_eq_reflect_of_code
    (order72_E9_code_of_gen_values h1 h2 (by decide))]; rfl⟩)))
    | exact Or.inr (Or.inr (Or.inr (⟨1, by rw [order72_E9_eq_order4_of_code
    (order72_E9_code_of_gen_values h1 h2 (by decide))]; rfl⟩)))
    | exact Or.inr (Or.inr (Or.inr (order72_E9_conj_order4_of_code_pow3
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inr (order72_E9_conj_order4_of_code_1112
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inr (order72_E9_conj_order4_of_code_2221
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inr (order72_E9_conj_order4_of_code_1222
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inr (order72_E9_conj_order4_of_code_2111
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exfalso
      have hg1 : (f ^ 4) order72_E9_g1 = order72_E9_g1 := by rw [hf]; rfl
      have hg2 : (f ^ 4) order72_E9_g2 = order72_E9_g2 := by rw [hf]; rfl
      rw [order72_E9_pow_eq_homOfValuesFun_iter f h1 h2 4 order72_E9_g1] at hg1
      rw [order72_E9_pow_eq_homOfValuesFun_iter f h1 h2 4 order72_E9_g2] at hg2
      have hpair : _ ∧ _ := ⟨hg1, hg2⟩
      exact absurd hpair (by decide)

/-! ### Centralizers of the standard involution and of the standard order-`4` element. -/

/-- An involution commuting with the standard reflection `diag(-1, 1)` lies in its
centralizer `{1, -I, diag(-1,1), diag(1,-1)}`. -/
theorem order72_E9_reflect_centralizer_sq_cases (g : MulAut (ElemAbelianRep 3))
    (hg2 : g ^ 2 = 1) (hcomm : Commute g order72_E9_reflectAut) :
    g = 1 ∨ g = order72_E9_negAut ∨ g = order72_E9_reflectAut ∨
      g = order72_E9_scaleSecond2 := by
  rcases order72_E9_total_cases (g order72_E9_g1) with h1 | h1 | h1 | h1 | h1 | h1 | h1 |
    h1 | h1 <;>
    rcases order72_E9_total_cases (g order72_E9_g2) with h2 | h2 | h2 | h2 | h2 | h2 | h2 |
      h2 | h2 <;>
    first
    | exact Or.inl (order72_E9_eq_one_of_code (order72_E9_code_of_gen_values h1 h2 (by decide)))
    | exact Or.inr (Or.inl (order72_E9_eq_neg_of_code
    (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_eq_reflect_of_code
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inr (order72_E9_eq_scaleSecond2_of_code
    (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exfalso
      have hg1 : (g ^ 2) order72_E9_g1 = order72_E9_g1 := by rw [hg2]; rfl
      have hg2 : (g ^ 2) order72_E9_g2 = order72_E9_g2 := by rw [hg2]; rfl
      rw [order72_E9_pow_eq_homOfValuesFun_iter g h1 h2 2 order72_E9_g1] at hg1
      rw [order72_E9_pow_eq_homOfValuesFun_iter g h1 h2 2 order72_E9_g2] at hg2
      have hc1 : (g * order72_E9_reflectAut) order72_E9_g1 =
          (order72_E9_reflectAut * g) order72_E9_g1 := by rw [hcomm.eq]
      have hc2 : (g * order72_E9_reflectAut) order72_E9_g2 =
          (order72_E9_reflectAut * g) order72_E9_g2 := by rw [hcomm.eq]
      simp only [MulAut.mul_apply, order72_E9_reflectAut_g1, order72_E9_reflectAut_g2,
        map_mul, map_pow, h1, h2] at hc1 hc2
      have hquad : _ ∧ _ ∧ _ ∧ _ := ⟨hg1, hg2, hc1, hc2⟩
      exact absurd hquad (by decide)

/-- An involution commuting with the standard order-`4` element is `1` or `-I`. -/
theorem order72_E9_order4_centralizer_sq_cases (g : MulAut (ElemAbelianRep 3))
    (hg2 : g ^ 2 = 1) (hcomm : Commute g order72_E9_order4Aut) :
    g = 1 ∨ g = order72_E9_negAut := by
  rcases order72_E9_total_cases (g order72_E9_g1) with h1 | h1 | h1 | h1 | h1 | h1 | h1 |
    h1 | h1 <;>
    rcases order72_E9_total_cases (g order72_E9_g2) with h2 | h2 | h2 | h2 | h2 | h2 | h2 |
      h2 | h2 <;>
    first
    | exact Or.inl (order72_E9_eq_one_of_code (order72_E9_code_of_gen_values h1 h2 (by decide)))
    | exact Or.inr (order72_E9_eq_neg_of_code (order72_E9_code_of_gen_values h1 h2 (by decide)))
    | exfalso
      have hg1 : (g ^ 2) order72_E9_g1 = order72_E9_g1 := by rw [hg2]; rfl
      have hg2 : (g ^ 2) order72_E9_g2 = order72_E9_g2 := by rw [hg2]; rfl
      rw [order72_E9_pow_eq_homOfValuesFun_iter g h1 h2 2 order72_E9_g1] at hg1
      rw [order72_E9_pow_eq_homOfValuesFun_iter g h1 h2 2 order72_E9_g2] at hg2
      have hc1 : (g * order72_E9_order4Aut) order72_E9_g1 =
          (order72_E9_order4Aut * g) order72_E9_g1 := by rw [hcomm.eq]
      have hc2 : (g * order72_E9_order4Aut) order72_E9_g2 =
          (order72_E9_order4Aut * g) order72_E9_g2 := by rw [hcomm.eq]
      simp only [MulAut.mul_apply, order72_E9_order4Aut_g1, order72_E9_order4Aut_g2,
        map_mul, map_pow, h1, h2] at hc1 hc2
      have hquad : _ ∧ _ ∧ _ ∧ _ := ⟨hg1, hg2, hc1, hc2⟩
      exact absurd hquad (by decide)

/-! ### Quaternion partners of the standard order-`4` element. -/

/-- The shear-conjugate of the standard order-`4` element: the second component of the
faithful quaternion pair (code `((1,1),(1,2))`). -/
noncomputable def order72_E9_order4Shear : MulAut (ElemAbelianRep 3) :=
  (MulAut.conj order72_E9_shearPlus) order72_E9_order4Aut

theorem order72_E9_order4Aut_pow3_g1 :
    (order72_E9_order4Aut ^ 3) order72_E9_g1 = order72_E9_g2 ^ 2 := by
  decide

theorem order72_E9_order4Aut_pow3_g2 :
    (order72_E9_order4Aut ^ 3) order72_E9_g2 = order72_E9_g1 := by
  decide

/-- **Quaternion partners of the standard order-`4` element**: the automorphisms `f`
with `f² = -I` and `f·R = R³·f` (where `R` is the standard order-`4` element) are
exactly `Rᵏ·S` for `k = 0,1,2,3`, with `S` the shear-conjugate.  The four surviving
codes are accepted directly; every other generator-image pair contradicts one of the
two constraints. -/
theorem order72_E9_order4_q8_partner_cases (f : MulAut (ElemAbelianRep 3))
    (hsq : f ^ 2 = order72_E9_negAut)
    (hconj : f * order72_E9_order4Aut = order72_E9_order4Aut ^ 3 * f) :
    f = order72_E9_order4Shear ∨ f = order72_E9_order4Aut * order72_E9_order4Shear ∨
      f = order72_E9_order4Aut ^ 2 * order72_E9_order4Shear ∨
        f = order72_E9_order4Aut ^ 3 * order72_E9_order4Shear := by
  rcases order72_E9_total_cases (f order72_E9_g1) with h1 | h1 | h1 | h1 | h1 | h1 | h1 |
    h1 | h1 <;>
    rcases order72_E9_total_cases (f order72_E9_g2) with h2 | h2 | h2 | h2 | h2 | h2 | h2 |
      h2 | h2 <;>
    first
    | exact Or.inl (order72_E9_autCode_injective
        (order72_E9_code_of_gen_values h1 h2 (by decide)))
    | exact Or.inr (Or.inl (order72_E9_autCode_injective
        (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_autCode_injective
        (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inr (order72_E9_autCode_injective
        (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exfalso
      have hg1 : (f ^ 2) order72_E9_g1 = order72_E9_negAut order72_E9_g1 := by rw [hsq]
      have hg2 : (f ^ 2) order72_E9_g2 = order72_E9_negAut order72_E9_g2 := by rw [hsq]
      rw [order72_E9_pow_eq_homOfValuesFun_iter f h1 h2 2 order72_E9_g1] at hg1
      rw [order72_E9_pow_eq_homOfValuesFun_iter f h1 h2 2 order72_E9_g2] at hg2
      rw [order72_E9_negAut_g1] at hg1
      rw [order72_E9_negAut_g2] at hg2
      have hc1 : (f * order72_E9_order4Aut) order72_E9_g1 =
          (order72_E9_order4Aut ^ 3 * f) order72_E9_g1 := by rw [hconj]
      have hc2 : (f * order72_E9_order4Aut) order72_E9_g2 =
          (order72_E9_order4Aut ^ 3 * f) order72_E9_g2 := by rw [hconj]
      simp only [MulAut.mul_apply, order72_E9_order4Aut_g1, order72_E9_order4Aut_g2,
        order72_E9_order4Aut_pow3_g1, order72_E9_order4Aut_pow3_g2,
        map_mul, map_pow, h1, h2] at hc1 hc2
      have hquad : _ ∧ _ ∧ _ ∧ _ := ⟨hg1, hg2, hc1, hc2⟩
      exact absurd hquad (by decide)

/-! ### Dihedral partners of the standard order-`4` element. -/

/-- The standard reflection times the standard order-`4` element is the swap. -/
theorem order72_E9_reflectAut_mul_order4Aut :
    order72_E9_reflectAut * order72_E9_order4Aut = order72_E9_swap := by
  apply order72_E9_aut_ext <;> decide

/-- The standard reflection times the cube of the standard order-`4` element is the
negated swap (the conjugate of the standard reflection by the negative-swap basis
change). -/
theorem order72_E9_reflectAut_mul_order4Aut_pow3 :
    order72_E9_reflectAut * order72_E9_order4Aut ^ 3 =
      (MulAut.conj order72_E9_negSwapReflectBasis) order72_E9_reflectAut := by
  apply order72_E9_aut_ext <;> decide

/-- **Dihedral partners of the standard order-`4` element**: the involutions `f` with
`f·R = R³·f` (where `R` is the standard order-`4` element) are exactly the four
reflections; pinned to the standard basis they are the standard reflection, the swap,
`diag(1,-1)` and the negated swap.  The four surviving codes are accepted directly;
every other generator-image pair contradicts one of the two constraints. -/
theorem order72_E9_order4_d4_partner_cases (f : MulAut (ElemAbelianRep 3))
    (hsq : f ^ 2 = 1)
    (hconj : f * order72_E9_order4Aut = order72_E9_order4Aut ^ 3 * f) :
    f = order72_E9_reflectAut ∨ f = order72_E9_swap ∨
      f = order72_E9_scaleSecond2 ∨
        f = (MulAut.conj order72_E9_negSwapReflectBasis) order72_E9_reflectAut := by
  rcases order72_E9_total_cases (f order72_E9_g1) with h1 | h1 | h1 | h1 | h1 | h1 | h1 |
    h1 | h1 <;>
    rcases order72_E9_total_cases (f order72_E9_g2) with h2 | h2 | h2 | h2 | h2 | h2 | h2 |
      h2 | h2 <;>
    first
    | exact Or.inl (order72_E9_eq_reflect_of_code
        (order72_E9_code_of_gen_values h1 h2 (by decide)))
    | exact Or.inr (Or.inl (order72_E9_autCode_injective
        (order72_E9_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (Or.inl (order72_E9_eq_scaleSecond2_of_code
        (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inr (order72_E9_autCode_injective
        (order72_E9_code_of_gen_values h1 h2 (by decide)))))
    | exfalso
      have hg1 : (f ^ 2) order72_E9_g1 = order72_E9_g1 := by rw [hsq]; rfl
      have hg2 : (f ^ 2) order72_E9_g2 = order72_E9_g2 := by rw [hsq]; rfl
      rw [order72_E9_pow_eq_homOfValuesFun_iter f h1 h2 2 order72_E9_g1] at hg1
      rw [order72_E9_pow_eq_homOfValuesFun_iter f h1 h2 2 order72_E9_g2] at hg2
      have hc1 : (f * order72_E9_order4Aut) order72_E9_g1 =
          (order72_E9_order4Aut ^ 3 * f) order72_E9_g1 := by rw [hconj]
      have hc2 : (f * order72_E9_order4Aut) order72_E9_g2 =
          (order72_E9_order4Aut ^ 3 * f) order72_E9_g2 := by rw [hconj]
      simp only [MulAut.mul_apply, order72_E9_order4Aut_g1, order72_E9_order4Aut_g2,
        order72_E9_order4Aut_pow3_g1, order72_E9_order4Aut_pow3_g2,
        map_mul, map_pow, h1, h2] at hc1 hc2
      have hquad : _ ∧ _ ∧ _ ∧ _ := ⟨hg1, hg2, hc1, hc2⟩
      exact absurd hquad (by decide)

end Smallgroups.UsefulTheorems
