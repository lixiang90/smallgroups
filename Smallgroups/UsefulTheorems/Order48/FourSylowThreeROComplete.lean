/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeROPresentation
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeReps

/-!
# Completion of the `S₄` quotient branch in order 48

The four normalized signed Coxeter presentations are identified with the
four previously constructed central double-cover representatives.
-/

namespace Smallgroups.UsefulTheorems

private theorem order48_signed_generators_generate_of_quotient
    {H Q : Type*} [Group H] [Group Q]
    (z a b c : H) (aQ bQ cQ : Q) (pi : H →* Q)
    (ha : pi a = aQ) (hb : pi b = bQ) (hc : pi c = cQ)
    (hQgen : Subgroup.closure (Set.range (order48_s4NormalGen aQ bQ cQ)) = ⊤)
    (hker : pi.ker = Subgroup.zpowers z) :
    Subgroup.closure (Set.range (order48_s4SignedGen z a b c)) = ⊤ := by
  let K := Subgroup.closure (Set.range (order48_s4SignedGen z a b c))
  have hzK : z ∈ K := Subgroup.subset_closure ⟨0, rfl⟩
  have haK : a ∈ K := Subgroup.subset_closure ⟨1, rfl⟩
  have hbK : b ∈ K := Subgroup.subset_closure ⟨2, rfl⟩
  have hcK : c ∈ K := Subgroup.subset_closure ⟨3, rfl⟩
  have hmaptop : K.map pi = ⊤ := by
    apply top_unique
    rw [← hQgen, Subgroup.closure_le]
    rintro q ⟨i, rfl⟩
    fin_cases i
    · exact ⟨a, haK, by simpa [order48_s4NormalGen] using ha⟩
    · exact ⟨b, hbK, by simpa [order48_s4NormalGen] using hb⟩
    · exact ⟨c, hcK, by simpa [order48_s4NormalGen] using hc⟩
  rw [Subgroup.eq_top_iff']
  intro x
  have hxmap : pi x ∈ K.map pi := by rw [hmaptop]; exact Subgroup.mem_top _
  obtain ⟨k, hkK, hk⟩ := hxmap
  let y := x * k⁻¹
  have hyker : y ∈ pi.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [y]
    rw [map_mul, map_inv, hk]
    group
  rw [hker] at hyker
  have hyK : y ∈ K := (Subgroup.zpowers_le.mpr hzK) hyker
  have hxy : x = y * k := by dsimp [y]; group
  rw [hxy]
  exact K.mul_mem hyK hkK

private def order48_RO_s01' : order24_RO := Equiv.swap (0 : Fin 4) 1
private def order48_RO_s12' : order24_RO := Equiv.swap (1 : Fin 4) 2
private def order48_RO_s23' : order24_RO := Equiv.swap (2 : Fin 4) 3

private theorem order48_RO_adjacent_generate :
    Subgroup.closure (Set.range (order48_s4NormalGen order48_RO_s01'
      order48_RO_s12' order48_RO_s23')) = ⊤ := by
  have hgen : order48_s4NormalGen order48_RO_s01' order48_RO_s12'
      order48_RO_s23' = (fun i : Fin 3 ↦ Equiv.swap i.castSucc i.succ) := by
    funext i
    fin_cases i <;> rfl
  rw [hgen]
  apply Subgroup.closure_eq_top_of_mclosure_eq_top
  exact Equiv.Perm.mclosure_swap_castSucc_succ 3

/-! ### The split cover (signs `0, 0`) -/

private def order48_RO00_z : order48_four_C2xS4 :=
  (Multiplicative.ofAdd (1 : ZMod 2), 1)
private def order48_RO00_a : order48_four_C2xS4 := (1, order48_RO_s01')
private def order48_RO00_b : order48_four_C2xS4 := (1, order48_RO_s12')
private def order48_RO00_c : order48_four_C2xS4 := (1, order48_RO_s23')

private theorem order48_RO00_z_center :
    order48_RO00_z ∈ Subgroup.center order48_four_C2xS4 := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨m, q⟩
  ext <;> simp [order48_RO00_z, mul_comm]

private theorem order48_RO00_ker_snd :
    (MonoidHom.snd (CyclicRep 2) order24_RO).ker =
      Subgroup.zpowers order48_RO00_z := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    rcases x with ⟨m, q⟩
    change q = 1 at hx
    subst q
    fin_cases m
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · apply Subgroup.zpowers_le.mpr
    rw [MonoidHom.mem_ker]
    rfl

private theorem order48_RO00_generate :
    Subgroup.closure (Set.range (order48_s4SignedGen order48_RO00_z
      order48_RO00_a order48_RO00_b order48_RO00_c)) = ⊤ := by
  apply order48_signed_generators_generate_of_quotient order48_RO00_z
    order48_RO00_a order48_RO00_b order48_RO00_c order48_RO_s01'
    order48_RO_s12' order48_RO_s23'
    (MonoidHom.snd (CyclicRep 2) order24_RO)
  · rfl
  · rfl
  · rfl
  · exact order48_RO_adjacent_generate
  · exact order48_RO00_ker_snd

/-- The `(0,0)` signed presentation is the split cover `C₂ × S₄`. -/
theorem order48_s4CoverPresentation_00_equiv_C2xS4 :
    Nonempty (order48_s4CoverPresentation 0 0 ≃* order48_four_C2xS4) := by
  apply nonempty_mulEquiv_s4CoverPresentation_of_card order48_RO00_z
    order48_RO00_a order48_RO00_b order48_RO00_c card_order48_four_C2xS4
  · exact order48_RO00_z_center
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact order48_RO00_generate

/-! ### The parity fibre product (signs `1, 0`) -/

private theorem order48_RO_C4Parity_two :
    order48_four_C4Parity (Multiplicative.ofAdd (2 : ZMod 4)) = 1 := by
  rw [show Multiplicative.ofAdd (2 : ZMod 4) =
      (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 by decide +kernel,
    map_pow, order48_four_C4Parity_gen]
  decide +kernel

private theorem order48_RO_C4Parity_three :
    order48_four_C4Parity (Multiplicative.ofAdd (3 : ZMod 4)) = -1 := by
  rw [show Multiplicative.ofAdd (3 : ZMod 4) =
      (Multiplicative.ofAdd (1 : ZMod 4)) ^ 3 by decide +kernel,
    map_pow, order48_four_C4Parity_gen]
  decide +kernel

private def order48_RO10_z : order48_four_C4fiberS4 :=
  ⟨(Multiplicative.ofAdd (2 : ZMod 4), 1), by
    rw [MonoidHom.mem_ker]
    simp [order48_four_C4S4ParityDiff, order48_RO_C4Parity_two]⟩

private def order48_RO10_a : order48_four_C4fiberS4 :=
  ⟨(Multiplicative.ofAdd (1 : ZMod 4), order48_RO_s01'), by
    rw [MonoidHom.mem_ker]
    simp [order48_four_C4S4ParityDiff, order48_RO_s01',
      order48_four_C4Parity_gen]⟩

private def order48_RO10_b : order48_four_C4fiberS4 :=
  ⟨(Multiplicative.ofAdd (3 : ZMod 4), order48_RO_s12'), by
    rw [MonoidHom.mem_ker]
    simp [order48_four_C4S4ParityDiff, order48_RO_s12',
      order48_RO_C4Parity_three]⟩

private def order48_RO10_c : order48_four_C4fiberS4 :=
  ⟨(Multiplicative.ofAdd (1 : ZMod 4), order48_RO_s23'), by
    rw [MonoidHom.mem_ker]
    simp [order48_four_C4S4ParityDiff, order48_RO_s23',
      order48_four_C4Parity_gen]⟩

private noncomputable def order48_RO10_toS4 :
    order48_four_C4fiberS4 →* order24_RO :=
  (MonoidHom.snd (CyclicRep 4) order24_RO).comp
    order48_four_C4S4ParityDiff.ker.subtype

private theorem order48_RO10_z_center :
    order48_RO10_z ∈ Subgroup.center order48_four_C4fiberS4 := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨⟨m, q⟩, hmq⟩
  apply Subtype.ext
  ext <;> simp [order48_RO10_z, mul_comm]

private theorem order48_RO10_ker_toS4 :
    order48_RO10_toS4.ker = Subgroup.zpowers order48_RO10_z := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    change x.1.2 = 1 at hx
    rcases x with ⟨⟨m, q⟩, hmq⟩
    change q = 1 at hx
    subst q
    have hmparity : order48_four_C4Parity m = 1 := by
      rw [MonoidHom.mem_ker] at hmq
      simpa [order48_four_C4S4ParityDiff] using hmq
    have hm_cases :
        m = Multiplicative.ofAdd (0 : ZMod 4) ∨
        m = Multiplicative.ofAdd (1 : ZMod 4) ∨
        m = Multiplicative.ofAdd (2 : ZMod 4) ∨
        m = Multiplicative.ofAdd (3 : ZMod 4) := by
      revert m
      decide +kernel
    rcases hm_cases with rfl | rfl | rfl | rfl
    · rw [show (⟨(Multiplicative.ofAdd (0 : ZMod 4), 1), _⟩ :
          order48_four_C4fiberS4) = 1 by apply Subtype.ext; rfl]
      exact Subgroup.one_mem _
    · rw [order48_four_C4Parity_gen] at hmparity
      exact ((by decide +kernel : (-1 : ℤˣ) ≠ 1) hmparity).elim
    · rw [show (⟨(Multiplicative.ofAdd (2 : ZMod 4), 1), _⟩ :
          order48_four_C4fiberS4) = order48_RO10_z by apply Subtype.ext; rfl]
      exact Subgroup.mem_zpowers _
    · rw [order48_RO_C4Parity_three] at hmparity
      exact ((by decide +kernel : (-1 : ℤˣ) ≠ 1) hmparity).elim
  · apply Subgroup.zpowers_le.mpr
    rw [MonoidHom.mem_ker]
    rfl

private theorem order48_RO10_generate :
    Subgroup.closure (Set.range (order48_s4SignedGen order48_RO10_z
      order48_RO10_a order48_RO10_b order48_RO10_c)) = ⊤ := by
  apply order48_signed_generators_generate_of_quotient order48_RO10_z
    order48_RO10_a order48_RO10_b order48_RO10_c order48_RO_s01'
    order48_RO_s12' order48_RO_s23' order48_RO10_toS4
  · rfl
  · rfl
  · rfl
  · exact order48_RO_adjacent_generate
  · exact order48_RO10_ker_toS4

/-- The `(1,0)` signed presentation is the parity fibre product
`C₄ ×_{C₂} S₄`. -/
theorem order48_s4CoverPresentation_10_equiv_C4fiberS4 :
    Nonempty (order48_s4CoverPresentation 1 0 ≃* order48_four_C4fiberS4) := by
  apply nonempty_mulEquiv_s4CoverPresentation_of_card order48_RO10_z
    order48_RO10_a order48_RO10_b order48_RO10_c card_order48_four_C4fiberS4
  · exact order48_RO10_z_center
  · apply Subtype.ext; decide +kernel
  · apply Subtype.ext; decide +kernel
  · apply Subtype.ext; decide +kernel
  · apply Subtype.ext; decide +kernel
  · apply Subtype.ext; decide +kernel
  · apply Subtype.ext; decide +kernel
  · apply Subtype.ext; decide +kernel
  · exact order48_RO10_generate

/-! ### The general linear cover (signs `0, 1`) -/

private def order48_RO01_z : order48_four_GL23 := -1

private def order48_RO01_a : order48_four_GL23 :=
  Matrix.GeneralLinearGroup.mk' !![0, 1; 1, 0]
    (invertibleOfNonzero (by decide +kernel))

private def order48_RO01_b : order48_four_GL23 :=
  Matrix.GeneralLinearGroup.mk' !![1, 0; -1, -1]
    (invertibleOfNonzero (by decide +kernel))

private def order48_RO01_c : order48_four_GL23 :=
  Matrix.GeneralLinearGroup.mk' !![1, 0; 0, -1]
    (invertibleOfNonzero (by decide +kernel))

private theorem order48_RO01_z_center :
    order48_RO01_z ∈ Subgroup.center order48_four_GL23 := by
  rw [Subgroup.mem_center_iff]
  intro x
  change x * (-1) = (-1) * x
  simp

set_option maxRecDepth 10000 in
private theorem order48_RO01_generate :
    Subgroup.closure (Set.range (order48_s4SignedGen order48_RO01_z
      order48_RO01_a order48_RO01_b order48_RO01_c)) = ⊤ := by
  apply s4_signed_generators_generate_of_normal_surjective
  intro x
  revert x
  decide +kernel

/-- The `(0,1)` signed presentation is `GL(2,3)`. -/
theorem order48_s4CoverPresentation_01_equiv_GL23 :
    Nonempty (order48_s4CoverPresentation 0 1 ≃* order48_four_GL23) := by
  apply nonempty_mulEquiv_s4CoverPresentation_of_card order48_RO01_z
    order48_RO01_a order48_RO01_b order48_RO01_c card_order48_four_GL23
  · exact order48_RO01_z_center
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact order48_RO01_generate

/-! ### The determinant-twist cover (signs `1, 1`) -/

private theorem order48_RO_signC4_two :
    order48_signC4 (Multiplicative.ofAdd (2 : ZMod 4)) = 1 := by
  rw [show Multiplicative.ofAdd (2 : ZMod 4) =
      (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 by decide +kernel,
    map_pow, order48_signC4_gen]
  decide +kernel

private theorem order48_RO_signC4_three :
    order48_signC4 (Multiplicative.ofAdd (3 : ZMod 4)) = -1 := by
  rw [show Multiplicative.ofAdd (3 : ZMod 4) =
      (Multiplicative.ofAdd (1 : ZMod 4)) ^ 3 by decide +kernel,
    map_pow, order48_signC4_gen]
  decide +kernel

private theorem order48_RO01_det_a :
    Matrix.GeneralLinearGroup.det order48_RO01_a = -1 := by
  decide +kernel

private theorem order48_RO01_det_b :
    Matrix.GeneralLinearGroup.det order48_RO01_b = -1 := by
  decide +kernel

private theorem order48_RO01_det_c :
    Matrix.GeneralLinearGroup.det order48_RO01_c = -1 := by
  decide +kernel

private def order48_RO11_z_parent : order48_four_C4fiberGL23 :=
  ⟨(Multiplicative.ofAdd (2 : ZMod 4), 1), by
    rw [MonoidHom.mem_ker]
    simp [order48_four_C4GL23DetDiff, order48_RO_signC4_two]⟩

private def order48_RO11_a_parent : order48_four_C4fiberGL23 :=
  ⟨(Multiplicative.ofAdd (1 : ZMod 4), order48_RO01_a), by
    rw [MonoidHom.mem_ker]
    simp [order48_four_C4GL23DetDiff, order48_signC4_gen,
      order48_RO01_det_a]⟩

private def order48_RO11_b_parent : order48_four_C4fiberGL23 :=
  ⟨(Multiplicative.ofAdd (3 : ZMod 4), order48_RO01_b), by
    rw [MonoidHom.mem_ker]
    simp [order48_four_C4GL23DetDiff, order48_RO_signC4_three,
      order48_RO01_det_b]⟩

private def order48_RO11_c_parent : order48_four_C4fiberGL23 :=
  ⟨(Multiplicative.ofAdd (1 : ZMod 4), order48_RO01_c), by
    rw [MonoidHom.mem_ker]
    simp [order48_four_C4GL23DetDiff, order48_signC4_gen,
      order48_RO01_det_c]⟩

private theorem order48_RO11_parent_relations :
    order48_RO11_z_parent ^ 2 = 1 ∧
    order48_RO11_a_parent ^ 2 = order48_RO11_z_parent ∧
    order48_RO11_b_parent ^ 2 = order48_RO11_z_parent ∧
    order48_RO11_c_parent ^ 2 = order48_RO11_z_parent ∧
    (order48_RO11_a_parent * order48_RO11_b_parent) ^ 3 = 1 ∧
    (order48_RO11_b_parent * order48_RO11_c_parent) ^ 3 = 1 ∧
    order48_RO11_a_parent * order48_RO11_c_parent *
        order48_RO11_a_parent⁻¹ * order48_RO11_c_parent⁻¹ =
      order48_RO11_z_parent * order48_four_C4fiberGL23Diagonal := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply Subtype.ext <;> decide +kernel

private noncomputable def order48_RO11_mk :
    order48_four_C4fiberGL23 →* order48_four_GL23DetTwist :=
  QuotientGroup.mk' (Subgroup.zpowers order48_four_C4fiberGL23Diagonal)

private noncomputable def order48_RO11_z : order48_four_GL23DetTwist :=
  order48_RO11_mk order48_RO11_z_parent
private noncomputable def order48_RO11_a : order48_four_GL23DetTwist :=
  order48_RO11_mk order48_RO11_a_parent
private noncomputable def order48_RO11_b : order48_four_GL23DetTwist :=
  order48_RO11_mk order48_RO11_b_parent
private noncomputable def order48_RO11_c : order48_four_GL23DetTwist :=
  order48_RO11_mk order48_RO11_c_parent

private theorem order48_RO11_z_parent_center :
    order48_RO11_z_parent ∈ Subgroup.center order48_four_C4fiberGL23 := by
  rw [Subgroup.mem_center_iff]
  rintro ⟨⟨m, q⟩, hmq⟩
  apply Subtype.ext
  ext <;> simp [order48_RO11_z_parent, mul_comm]

private theorem order48_RO11_z_center :
    order48_RO11_z ∈ Subgroup.center order48_four_GL23DetTwist := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨y, rfl⟩ := (QuotientGroup.mk'_surjective
    (Subgroup.zpowers order48_four_C4fiberGL23Diagonal)) x
  exact congrArg order48_RO11_mk
    (Subgroup.mem_center_iff.mp order48_RO11_z_parent_center y)

private theorem order48_RO11_relations :
    order48_RO11_z ^ 2 = 1 ∧
    order48_RO11_a ^ 2 = order48_RO11_z ∧
    order48_RO11_b ^ 2 = order48_RO11_z ∧
    order48_RO11_c ^ 2 = order48_RO11_z ∧
    (order48_RO11_a * order48_RO11_b) ^ 3 = 1 ∧
    (order48_RO11_b * order48_RO11_c) ^ 3 = 1 ∧
    order48_RO11_a * order48_RO11_c * order48_RO11_a⁻¹ * order48_RO11_c⁻¹ =
      order48_RO11_z := by
  obtain ⟨hz2, ha2, hb2, hc2, hab3, hbc3, hac⟩ := order48_RO11_parent_relations
  have hdiag : order48_RO11_mk order48_four_C4fiberGL23Diagonal = 1 := by
    change (order48_four_C4fiberGL23Diagonal : order48_four_GL23DetTwist) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_zpowers _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [order48_RO11_z] using congrArg order48_RO11_mk hz2
  · simpa [order48_RO11_z, order48_RO11_a] using congrArg order48_RO11_mk ha2
  · simpa [order48_RO11_z, order48_RO11_b] using congrArg order48_RO11_mk hb2
  · simpa [order48_RO11_z, order48_RO11_c] using congrArg order48_RO11_mk hc2
  · simpa [order48_RO11_a, order48_RO11_b] using congrArg order48_RO11_mk hab3
  · simpa [order48_RO11_b, order48_RO11_c] using congrArg order48_RO11_mk hbc3
  · simpa [order48_RO11_z, order48_RO11_a, order48_RO11_c, hdiag] using
      congrArg order48_RO11_mk hac

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Kernel-checking the 96-by-48 parent normal-form cover needs extra reductions.
private theorem order48_RO11_generate :
    Subgroup.closure (Set.range (order48_s4SignedGen order48_RO11_z
      order48_RO11_a order48_RO11_b order48_RO11_c)) = ⊤ := by
  have hcover : ∀ p : order48_four_C4fiberGL23,
      ∃ q : Fin 2 × Fin 24,
        p.1 = (order48_s4SignedNormal order48_RO11_z_parent
          order48_RO11_a_parent order48_RO11_b_parent order48_RO11_c_parent q).1 ∨
        p.1 = (order48_s4SignedNormal order48_RO11_z_parent
          order48_RO11_a_parent order48_RO11_b_parent order48_RO11_c_parent q *
            order48_four_C4fiberGL23Diagonal).1 := by
    intro p
    revert p
    decide +kernel
  have hdiag : order48_RO11_mk order48_four_C4fiberGL23Diagonal = 1 := by
    change (order48_four_C4fiberGL23Diagonal : order48_four_GL23DetTwist) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_zpowers _
  apply s4_signed_generators_generate_of_normal_surjective
  intro x
  obtain ⟨p, rfl⟩ := (QuotientGroup.mk'_surjective
    (Subgroup.zpowers order48_four_C4fiberGL23Diagonal)) x
  obtain ⟨q, hq⟩ := hcover p
  have hmap : order48_RO11_mk
        (order48_s4SignedNormal order48_RO11_z_parent
          order48_RO11_a_parent order48_RO11_b_parent order48_RO11_c_parent q) =
      order48_s4SignedNormal order48_RO11_z order48_RO11_a
        order48_RO11_b order48_RO11_c q := by
    simp [order48_RO11_z, order48_RO11_a, order48_RO11_b, order48_RO11_c]
  rcases hq with hq | hq
  · refine ⟨q, ?_⟩
    rw [← hmap]
    exact congrArg order48_RO11_mk (Subtype.ext hq).symm
  · refine ⟨q, ?_⟩
    rw [← hmap]
    change order48_RO11_mk _ = order48_RO11_mk p
    have hp := congrArg order48_RO11_mk (Subtype.ext hq)
    simpa [hdiag] using hp.symm

/-- The `(1,1)` signed presentation is the determinant twist of `GL(2,3)`. -/
theorem order48_s4CoverPresentation_11_equiv_GL23DetTwist :
    Nonempty (order48_s4CoverPresentation 1 1 ≃* order48_four_GL23DetTwist) := by
  obtain ⟨hz2, ha2, hb2, hc2, hab3, hbc3, hac⟩ := order48_RO11_relations
  apply nonempty_mulEquiv_s4CoverPresentation_of_card order48_RO11_z
    order48_RO11_a order48_RO11_b order48_RO11_c
    card_order48_four_GL23DetTwist
  · exact order48_RO11_z_center
  · exact hz2
  · simpa using ha2
  · simpa using hb2
  · simpa using hc2
  · exact hab3
  · exact hbc3
  · simpa using hac
  · exact order48_RO11_generate

/-- Every central `C₂`-extension of `S₄` is one of the four residual
representatives with indices `0`, `1`, `2`, and `7`. -/
theorem order48_RO_cocycle_exhaustive :
    Order48FourCocycleExhaustive order24_RO := by
  intro f hf
  obtain ⟨sq, cm, e⟩ := order48_RO_cocycle_is_signed_presentation f hf
  fin_cases sq <;> fin_cases cm
  · refine ⟨0, ?_⟩
    change Nonempty (CocycleGroup f hf ≃* order48_four_C2xS4)
    exact ⟨e.some.symm.trans order48_s4CoverPresentation_00_equiv_C2xS4.some⟩
  · refine ⟨1, ?_⟩
    change Nonempty (CocycleGroup f hf ≃* order48_four_GL23)
    exact ⟨e.some.symm.trans order48_s4CoverPresentation_01_equiv_GL23.some⟩
  · refine ⟨2, ?_⟩
    change Nonempty (CocycleGroup f hf ≃* order48_four_C4fiberS4)
    exact ⟨e.some.symm.trans order48_s4CoverPresentation_10_equiv_C4fiberS4.some⟩
  · refine ⟨7, ?_⟩
    change Nonempty (CocycleGroup f hf ≃* order48_four_GL23DetTwist)
    exact ⟨e.some.symm.trans order48_s4CoverPresentation_11_equiv_GL23DetTwist.some⟩

end Smallgroups.UsefulTheorems
