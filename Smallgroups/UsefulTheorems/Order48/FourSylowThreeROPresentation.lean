/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeS4NormalForm

/-!
# A two-bit presentation for central double covers of `S₄`

Lifts of the three adjacent transpositions can be normalized so that the two
braid products have order three.  Their common square and the commutator of
the distant lifts are then the only two central signs.
-/

namespace Smallgroups.UsefulTheorems

private def order48_RO_s01 : order24_RO := Equiv.swap (0 : Fin 4) 1
private def order48_RO_s12 : order24_RO := Equiv.swap (1 : Fin 4) 2
private def order48_RO_s23 : order24_RO := Equiv.swap (2 : Fin 4) 3

private def order48_RO_z
    {f : order24_RO → order24_RO → ZMod 2} (hf : IsCentralCocycle f) :
    CocycleGroup f hf :=
  CocycleGroup.inl (hf := hf) (Multiplicative.ofAdd (1 : ZMod 2))

private theorem order48_RO_snd_one_mem_center
    {f : order24_RO → order24_RO → ZMod 2} {hf : IsCentralCocycle f}
    {x : CocycleGroup f hf} (hx : x.snd = 1) :
    x ∈ Subgroup.center (CocycleGroup f hf) := by
  have hxker : x ∈ (CocycleGroup.rightHom (hf := hf)).ker := by
    rw [MonoidHom.mem_ker]
    exact hx
  rw [CocycleGroup.ker_rightHom] at hxker
  obtain ⟨m, rfl⟩ := hxker
  exact CocycleGroup.inl_mem_center m

private theorem order48_RO_snd_one_sq
    {f : order24_RO → order24_RO → ZMod 2} {hf : IsCentralCocycle f}
    {x : CocycleGroup f hf} (hx : x.snd = 1) : x ^ 2 = 1 := by
  have hxker : x ∈ (CocycleGroup.rightHom (hf := hf)).ker := by
    rw [MonoidHom.mem_ker]
    exact hx
  rw [CocycleGroup.ker_rightHom] at hxker
  obtain ⟨m, rfl⟩ := hxker
  rw [← map_pow]
  have hm : m ^ 2 = 1 := by
    fin_cases m <;> decide +kernel
  rw [hm, map_one]

private theorem order48_RO_snd_one_eq_zpow
    {f : order24_RO → order24_RO → ZMod 2} {hf : IsCentralCocycle f}
    (x : CocycleGroup f hf) (hx : x.snd = 1) :
    x = order48_RO_z hf ^ x.fst.val := by
  rcases x with ⟨m, q⟩
  change q = 1 at hx
  subst q
  change CocycleGroup.inl (hf := hf) (Multiplicative.ofAdd m) =
    CocycleGroup.inl (hf := hf) (Multiplicative.ofAdd (1 : ZMod 2)) ^ m.val
  rw [← map_pow]
  have hm : Multiplicative.ofAdd m =
      (Multiplicative.ofAdd (1 : ZMod 2)) ^ m.val := by
    fin_cases m <;> decide +kernel
  exact congrArg (CocycleGroup.inl (hf := hf)) hm

private theorem order48_RO_square_eq_of_snd_conjugate
    {f : order24_RO → order24_RO → ZMod 2} {hf : IsCentralCocycle f}
    (x y g : CocycleGroup f hf)
    (hx2 : x.snd ^ 2 = 1) (hy2 : y.snd ^ 2 = 1)
    (hconj : g.snd * x.snd * g.snd⁻¹ = y.snd) :
    x ^ 2 = y ^ 2 := by
  let y' := g * x * g⁻¹
  let k := y' * y⁻¹
  have hx2snd : (x ^ 2).snd = 1 := by
    change x.snd * x.snd = 1
    simpa [pow_two] using hx2
  have hy2snd : (y ^ 2).snd = 1 := by
    change y.snd * y.snd = 1
    simpa [pow_two] using hy2
  have hy'snd : y'.snd = y.snd := by
    change g.snd * x.snd * g.snd⁻¹ = y.snd
    exact hconj
  have hksnd : k.snd = 1 := by
    change y'.snd * y.snd⁻¹ = 1
    rw [hy'snd]
    group
  have hx2center := order48_RO_snd_one_mem_center hx2snd
  have hkcenter := order48_RO_snd_one_mem_center hksnd
  have hk2 := order48_RO_snd_one_sq hksnd
  have hy'eq : y' = k * y := by
    dsimp [k]
    group
  have hy'2_eq_x2 : y' ^ 2 = x ^ 2 := by
    dsimp [y']
    calc
      (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by
        simp only [pow_two]
        group
      _ = x ^ 2 := by
        have hc := (Subgroup.mem_center_iff.mp hx2center) g
        rw [hc]
        group
  calc
    x ^ 2 = y' ^ 2 := hy'2_eq_x2.symm
    _ = (k * y) ^ 2 := by rw [hy'eq]
    _ = k ^ 2 * y ^ 2 := by
      have hky : Commute k y :=
        (Subgroup.mem_center_iff.mp hkcenter y).symm
      exact hky.mul_pow 2
    _ = y ^ 2 := by rw [hk2, one_mul]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3200000 in
-- Normalizing arbitrary cocycle lifts requires several symbolic noncommutative reductions.
/-- Every central `C₂`-extension of `S₄` has normalized Coxeter lifts governed
by two signs `squareSign` and `commutatorSign`. -/
theorem order48_RO_cocycle_normalized_two_bit_presentation
    (f : order24_RO → order24_RO → ZMod 2) (hf : IsCentralCocycle f) :
    ∃ (z a b c : CocycleGroup f hf) (squareSign commutatorSign : ZMod 2),
      z ∈ Subgroup.center (CocycleGroup f hf) ∧
      z ^ 2 = 1 ∧ z ≠ 1 ∧
      (CocycleGroup.rightHom (hf := hf)) a = order48_RO_s01 ∧
      (CocycleGroup.rightHom (hf := hf)) b = order48_RO_s12 ∧
      (CocycleGroup.rightHom (hf := hf)) c = order48_RO_s23 ∧
      a ^ 2 = z ^ squareSign.val ∧
      b ^ 2 = z ^ squareSign.val ∧
      c ^ 2 = z ^ squareSign.val ∧
      (a * b) ^ 3 = 1 ∧ (b * c) ^ 3 = 1 ∧
      a * c * a⁻¹ * c⁻¹ = z ^ commutatorSign.val := by
  let z := order48_RO_z hf
  let a0 : CocycleGroup f hf := ⟨0, order48_RO_s01⟩
  let b : CocycleGroup f hf := ⟨0, order48_RO_s12⟩
  let c0 : CocycleGroup f hf := ⟨0, order48_RO_s23⟩
  let u := (a0 * b) ^ 3
  let v := (b * c0) ^ 3
  let a := u * a0
  let c := c0 * v
  have huz : u.snd = 1 := by
    change (order48_RO_s01 * order48_RO_s12) ^ 3 = 1
    dsimp [order48_RO_s01, order48_RO_s12]
    decide +kernel
  have hvz : v.snd = 1 := by
    change (order48_RO_s12 * order48_RO_s23) ^ 3 = 1
    dsimp [order48_RO_s12, order48_RO_s23]
    decide +kernel
  have hu2 : u ^ 2 = 1 := order48_RO_snd_one_sq huz
  have hv2 : v ^ 2 = 1 := order48_RO_snd_one_sq hvz
  have hucenter := order48_RO_snd_one_mem_center huz
  have hvcenter := order48_RO_snd_one_mem_center hvz
  have hab3 : (a * b) ^ 3 = 1 := by
    have hcomm : Commute u (a0 * b) :=
      (Subgroup.mem_center_iff.mp hucenter (a0 * b)).symm
    change (u * a0 * b) ^ 3 = 1
    rw [show u * a0 * b = u * (a0 * b) by group, hcomm.mul_pow]
    change u ^ 3 * u = 1
    rw [show u ^ 3 = u by
      calc
        u ^ 3 = u ^ 2 * u := by rw [pow_succ]
        _ = u := by rw [hu2, one_mul]]
    simpa only [pow_two] using hu2
  have hbc3 : (b * c) ^ 3 = 1 := by
    have hcomm : Commute v (b * c0) :=
      (Subgroup.mem_center_iff.mp hvcenter (b * c0)).symm
    change (b * (c0 * v)) ^ 3 = 1
    rw [show b * (c0 * v) = v * (b * c0) by
          calc
            b * (c0 * v) = (b * c0) * v := by group
            _ = v * (b * c0) := hcomm.eq.symm,
      hcomm.mul_pow]
    change v ^ 3 * v = 1
    rw [show v ^ 3 = v by
      calc
        v ^ 3 = v ^ 2 * v := by rw [pow_succ]
        _ = v := by rw [hv2, one_mul]]
    simpa only [pow_two] using hv2
  have ha_snd : a.snd = order48_RO_s01 := by
    change u.snd * order48_RO_s01 = order48_RO_s01
    rw [huz, one_mul]
  have hb_snd : b.snd = order48_RO_s12 := rfl
  have hc_snd : c.snd = order48_RO_s23 := by
    change order48_RO_s23 * v.snd = order48_RO_s23
    rw [hvz, mul_one]
  have hs01 : order48_RO_s01 ^ 2 = 1 := by decide +kernel
  have hs12 : order48_RO_s12 ^ 2 = 1 := by decide +kernel
  have hs23 : order48_RO_s23 ^ 2 = 1 := by decide +kernel
  have hconj01 :
      (order48_RO_s01 * order48_RO_s12) * a.snd *
        (order48_RO_s01 * order48_RO_s12)⁻¹ = b.snd := by
    rw [ha_snd, hb_snd]
    dsimp [order48_RO_s01, order48_RO_s12]
    decide +kernel
  have hconj12 :
      (order48_RO_s12 * order48_RO_s23) * b.snd *
        (order48_RO_s12 * order48_RO_s23)⁻¹ = c.snd := by
    rw [hb_snd, hc_snd]
    dsimp [order48_RO_s12, order48_RO_s23]
    decide +kernel
  have habsq : a ^ 2 = b ^ 2 :=
    order48_RO_square_eq_of_snd_conjugate a b
      (⟨0, order48_RO_s01 * order48_RO_s12⟩ : CocycleGroup f hf)
      (by rw [ha_snd]; exact hs01) (by rw [hb_snd]; exact hs12) hconj01
  have hbcsq : b ^ 2 = c ^ 2 :=
    order48_RO_square_eq_of_snd_conjugate b c
      (⟨0, order48_RO_s12 * order48_RO_s23⟩ : CocycleGroup f hf)
      (by rw [hb_snd]; exact hs12) (by rw [hc_snd]; exact hs23) hconj12
  have ha2snd : (a ^ 2).snd = 1 := by
    change a.snd * a.snd = 1
    rw [ha_snd]
    simpa [pow_two] using hs01
  let squareSign : ZMod 2 := (a ^ 2).fst
  have ha2sign : a ^ 2 = z ^ squareSign.val :=
    order48_RO_snd_one_eq_zpow (a ^ 2) ha2snd
  let d := a * c * a⁻¹ * c⁻¹
  have hdsnd : d.snd = 1 := by
    dsimp [d]
    rw [ha_snd, hc_snd]
    dsimp [order48_RO_s01, order48_RO_s23]
    decide +kernel
  let commutatorSign : ZMod 2 := d.fst
  have hdsign : d = z ^ commutatorSign.val :=
    order48_RO_snd_one_eq_zpow d hdsnd
  have hzcenter : z ∈ Subgroup.center (CocycleGroup f hf) :=
    CocycleGroup.inl_mem_center _
  have hz2 : z ^ 2 = 1 := by
    dsimp [z, order48_RO_z]
    rw [← map_pow]
    have hm : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by
      decide +kernel
    rw [hm, map_one]
  have hzne : z ≠ 1 := by
    intro h
    have h' := CocycleGroup.inl_injective h
    exact (by decide +kernel :
      Multiplicative.ofAdd (1 : ZMod 2) ≠ 1) h'
  refine ⟨z, a, b, c, squareSign, commutatorSign,
    hzcenter, hz2, hzne, ha_snd, hb_snd, hc_snd, ha2sign, ?_, ?_, hab3, hbc3, hdsign⟩
  · rw [← habsq]
    exact ha2sign
  · rw [← hbcsq, ← habsq]
    exact ha2sign

end Smallgroups.UsefulTheorems
