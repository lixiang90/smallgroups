/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PQ
import Smallgroups.UsefulTheorems.Order2PSqElem
import Smallgroups.UsefulTheorems.PrimeSqPrimeAbelian
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Mathlib.Tactic.NormNum.Prime

/-!
# First structural reductions for groups of order 90

The order `90 = 2 * 45` has odd half-order.  The sign of the left regular action
therefore gives an index-two normal subgroup, and Schur--Zassenhaus splits over it.
-/

namespace Smallgroups.UsefulTheorems

open Subgroup

variable {G : Type*} [Group G]

/-! ### The cyclic order-45 kernel -/

abbrev order90_C2 : Type := CyclicRep 2
abbrev order90_C3 : Type := CyclicRep 3
abbrev order90_C5 : Type := CyclicRep 5
abbrev order90_C9 : Type := CyclicRep 9
abbrev order90_C45 : Type := CyclicRep 45
abbrev order90_C90 : Type := CyclicRep 90
abbrev order90_D45 : Type := DihedralGroup 45
abbrev order90_E33 : Type := ElemAbelianRep 3
abbrev order90_E33C5 : Type := order90_E33 × order90_C5
abbrev order90_C9D5 : Type := order90_C9 × DihedralGroup 5
abbrev order90_C5D9 : Type := order90_C5 × DihedralGroup 9

noncomputable abbrev order90_u19 : (ZMod 45)ˣ :=
  ZMod.unitOfCoprime 19 (by norm_num : Nat.Coprime 19 45)

noncomputable abbrev order90_u26 : (ZMod 45)ˣ :=
  ZMod.unitOfCoprime 26 (by norm_num : Nat.Coprime 26 45)

noncomputable abbrev order90_u44 : (ZMod 45)ˣ :=
  ZMod.unitOfCoprime 44 (by norm_num : Nat.Coprime 44 45)

theorem order90_u19_sq : order90_u19 ^ 2 = 1 := by
  decide

theorem order90_u26_sq : order90_u26 ^ 2 = 1 := by
  decide

theorem order90_u44_sq : order90_u44 ^ 2 = 1 := by
  decide

noncomputable abbrev order90_c45UnitHom (u : (ZMod 45)ˣ) (hu : u ^ 2 = 1) :
    order90_C2 →* (ZMod 45)ˣ :=
  powHom (p := 45) (q := 2) u hu

noncomputable abbrev order90_c45Action (u : (ZMod 45)ˣ) (hu : u ^ 2 = 1) :
    order90_C2 →* MulAut order90_C45 :=
  unitAutHom.comp (order90_c45UnitHom u hu)

noncomputable abbrev order90_c45Action_trivial : order90_C2 →* MulAut order90_C45 :=
  order90_c45Action 1 (by simp)

noncomputable abbrev order90_c45Action_19 : order90_C2 →* MulAut order90_C45 :=
  order90_c45Action order90_u19 order90_u19_sq

noncomputable abbrev order90_c45Action_26 : order90_C2 →* MulAut order90_C45 :=
  order90_c45Action order90_u26 order90_u26_sq

noncomputable abbrev order90_c45Action_44 : order90_C2 →* MulAut order90_C45 :=
  order90_c45Action order90_u44 order90_u44_sq

theorem order90_unit_sq_eq_one_cases (u : (ZMod 45)ˣ) (hu : u ^ 2 = 1) :
    u = 1 ∨ u = order90_u19 ∨ u = order90_u26 ∨ u = order90_u44 := by
  decide +revert

/-- Multiplication by units embeds into the automorphism group of `C₄₅`. -/
theorem order90_unitAutHom_injective : Function.Injective (unitAutHom (p := 45)) := by
  intro u v h
  have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod 45)) =
      unitAutHom v (Multiplicative.ofAdd (1 : ZMod 45)) := by rw [h]
  simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
  exact Units.ext (congrArg Multiplicative.toAdd h1)

/-- Every automorphism of `C₄₅` is multiplication by a unit of `ZMod 45`. -/
theorem order90_mulAut_eq_unitAutHom (σ : MulAut order90_C45) :
    ∃ u : (ZMod 45)ˣ, σ = unitAutHom u := by
  let f : AddAut (ZMod 45) := Multiplicative.toAdd ((MulAutMultiplicative (ZMod 45)) σ)
  let u : (ZMod 45)ˣ := Additive.toMul ((ZMod.AddAutEquivUnits 45) f)
  refine ⟨u, ?_⟩
  ext x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  change Multiplicative.ofAdd (f m) = unitAutHom u (Multiplicative.ofAdd m)
  have hu : Additive.ofMul u = (ZMod.AddAutEquivUnits 45) f := by simp [u]
  have hf : f = (ZMod.AddAutEquivUnits 45).symm (Additive.ofMul u) := by
    symm
    rw [hu]
    exact AddEquiv.symm_apply_apply (ZMod.AddAutEquivUnits 45) f
  rw [hf, unitAutHom_apply]
  simp [ZMod.AddAutEquivUnits_symm_apply, Units.smul_def]

theorem order90_c45UnitHom_gen (u : (ZMod 45)ˣ) (hu : u ^ 2 = 1) :
    order90_c45UnitHom u hu (Multiplicative.ofAdd (1 : ZMod 2)) = u := by
  change u ^ ((1 : ZMod 2).val) = u
  rw [show (1 : ZMod 2).val = 1 from by decide, pow_one]

theorem order90_c45Action_gen (u : (ZMod 45)ˣ) (hu : u ^ 2 = 1) :
    order90_c45Action u hu (Multiplicative.ofAdd (1 : ZMod 2)) = unitAutHom u := by
  change unitAutHom (order90_c45UnitHom u hu (Multiplicative.ofAdd (1 : ZMod 2))) =
    unitAutHom u
  rw [order90_c45UnitHom_gen]

theorem order90_c45Action_trivial_gen :
    order90_c45Action_trivial (Multiplicative.ofAdd (1 : ZMod 2)) =
      unitAutHom (p := 45) 1 :=
  order90_c45Action_gen 1 (by simp)

theorem order90_c45Action_19_gen :
    order90_c45Action_19 (Multiplicative.ofAdd (1 : ZMod 2)) = unitAutHom order90_u19 :=
  order90_c45Action_gen order90_u19 order90_u19_sq

theorem order90_c45Action_26_gen :
    order90_c45Action_26 (Multiplicative.ofAdd (1 : ZMod 2)) = unitAutHom order90_u26 :=
  order90_c45Action_gen order90_u26 order90_u26_sq

theorem order90_c45Action_44_gen :
    order90_c45Action_44 (Multiplicative.ofAdd (1 : ZMod 2)) = unitAutHom order90_u44 :=
  order90_c45Action_gen order90_u44 order90_u44_sq

private theorem order90_c2_cases (x : order90_C2) :
    x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) := by
  fin_cases x <;> decide

theorem order90_c2_action_hom_ext {φ ψ : order90_C2 →* MulAut order90_C45}
    (hgen : φ (Multiplicative.ofAdd (1 : ZMod 2)) =
      ψ (Multiplicative.ofAdd (1 : ZMod 2))) :
    φ = ψ := by
  apply MonoidHom.ext
  intro h
  rcases order90_c2_cases h with rfl | rfl
  · simp
  · exact hgen

theorem order90_c45_action_cases (φ : order90_C2 →* MulAut order90_C45) :
    φ = order90_c45Action_trivial ∨ φ = order90_c45Action_19 ∨
      φ = order90_c45Action_26 ∨ φ = order90_c45Action_44 := by
  let gen : order90_C2 := Multiplicative.ofAdd (1 : ZMod 2)
  let α := φ gen
  have hgen_two : gen ^ 2 = 1 := by
    decide
  have hα2 : α ^ 2 = 1 := by
    calc
      α ^ 2 = φ (gen ^ 2) := by rw [map_pow]
      _ = φ 1 := by rw [hgen_two]
      _ = 1 := map_one _
  obtain ⟨u, huα⟩ := order90_mulAut_eq_unitAutHom α
  have huα2 : (unitAutHom (p := 45) u) ^ 2 = 1 := by
    rw [← huα]
    exact hα2
  have hu2 : u ^ 2 = 1 := by
    apply order90_unitAutHom_injective
    calc
      unitAutHom (p := 45) (u ^ 2) = (unitAutHom (p := 45) u) ^ 2 := by
        rw [map_pow]
      _ = 1 := huα2
      _ = unitAutHom (p := 45) 1 := by rw [map_one]
  rcases order90_unit_sq_eq_one_cases u hu2 with hu | hu | hu | hu
  · left
    apply order90_c2_action_hom_ext
    change α = order90_c45Action_trivial gen
    rw [huα, hu, order90_c45Action_trivial_gen]
  · right
    left
    apply order90_c2_action_hom_ext
    change α = order90_c45Action_19 gen
    rw [huα, hu, order90_c45Action_19_gen]
  · right
    right
    left
    apply order90_c2_action_hom_ext
    change α = order90_c45Action_26 gen
    rw [huα, hu, order90_c45Action_26_gen]
  · right
    right
    right
    apply order90_c2_action_hom_ext
    change α = order90_c45Action_44 gen
    rw [huα, hu, order90_c45Action_44_gen]

noncomputable def order90_c45_trivial_prod_iso :
    order90_C45 × order90_C2 ≃* order90_C90 := by
  have hcop : (45 : ℕ).Coprime 2 := by norm_num
  let e_crt : ZMod (45 * 2) ≃+* ZMod 45 × ZMod 2 := ZMod.chineseRemainder hcop
  let e_add : Multiplicative (ZMod (45 * 2)) ≃* Multiplicative (ZMod 45 × ZMod 2) :=
    AddEquiv.toMultiplicative e_crt.toAddEquiv
  let e_prod : Multiplicative (ZMod 45 × ZMod 2) ≃*
      Multiplicative (ZMod 45) × Multiplicative (ZMod 2) :=
    MulEquiv.prodMultiplicative (ZMod 45) (ZMod 2)
  let e_mul : order90_C90 ≃* Multiplicative (ZMod (45 * 2)) := by
    refine AddEquiv.toMultiplicative (ZMod.ringEquivCongr ?_).toAddEquiv
    norm_num
  exact (e_mul.trans (e_add.trans e_prod)).symm

noncomputable def order90_c45_trivial_semidirect_iso :
    SemidirectProduct order90_C45 order90_C2
      (1 : order90_C2 →* MulAut order90_C45) ≃* order90_C90 := by
  let e : SemidirectProduct order90_C45 order90_C2
      (1 : order90_C2 →* MulAut order90_C45) ≃* order90_C45 × order90_C2 :=
    { toEquiv := SemidirectProduct.equivProd
      map_mul' := fun x y => by
        rcases x with ⟨n₁, h₁⟩
        rcases y with ⟨n₂, h₂⟩
        simp }
  exact e.trans order90_c45_trivial_prod_iso

theorem order90_c45Action_trivial_eq_one :
    order90_c45Action_trivial = (1 : order90_C2 →* MulAut order90_C45) := by
  apply order90_c2_action_hom_ext
  rw [order90_c45Action_trivial_gen]
  exact map_one (unitAutHom (p := 45))

theorem order90_c45_trivial_action_semidirect_iso :
    Nonempty (SemidirectProduct order90_C45 order90_C2
      order90_c45Action_trivial ≃* order90_C90) := by
  exact ⟨(semidirectProductCongr_eq order90_c45Action_trivial_eq_one).trans
    order90_c45_trivial_semidirect_iso⟩

theorem order90_unitAutHom_u44_eq_inv :
    unitAutHom order90_u44 = invAut order90_C45 := by
  ext x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [unitAutHom_apply, invAut_apply]
  have h : (order90_u44 : ZMod 45) * m = -m := by
    simp only [order90_u44, ZMod.unitOfCoprime, Units.val_mk]
    change (44 : ZMod 45) * m = -m
    have h44 : (44 : ZMod 45) = -1 := by decide
    rw [h44]
    simp
  simpa [h]

theorem order90_c45Action_44_eq_invAction :
    order90_c45Action_44 = invActionHom order90_C45 := by
  apply order90_c2_action_hom_ext
  rw [order90_c45Action_44_gen, invActionHom_ofAdd_one, order90_unitAutHom_u44_eq_inv]

theorem order90_c45_inv_semidirect_iso :
    Nonempty (SemidirectProduct order90_C45 order90_C2
      order90_c45Action_44 ≃* order90_D45) := by
  haveI : NeZero 45 := ⟨by norm_num⟩
  exact ⟨(semidirectProductCongr_eq order90_c45Action_44_eq_invAction).trans
    (genDihedralCyclicIso 45)⟩

noncomputable def order90_c45_crt_iso_9_5 : order90_C45 ≃* order90_C9 × order90_C5 := by
  have hcop : (9 : ℕ).Coprime 5 := by norm_num
  let e_mul : order90_C45 ≃* Multiplicative (ZMod (9 * 5)) := by
    refine AddEquiv.toMultiplicative (ZMod.ringEquivCongr ?_).toAddEquiv
    norm_num
  exact e_mul.trans (crtProd 9 5 hcop).symm

noncomputable def order90_c45_crt_iso_5_9 : order90_C45 ≃* order90_C5 × order90_C9 := by
  have hcop : (5 : ℕ).Coprime 9 := by norm_num
  let e_mul : order90_C45 ≃* Multiplicative (ZMod (5 * 9)) := by
    refine AddEquiv.toMultiplicative (ZMod.ringEquivCongr ?_).toAddEquiv
    norm_num
  exact e_mul.trans (crtProd 5 9 hcop).symm

noncomputable abbrev order90_c9c5Action_19 :
    order90_C2 →* MulAut (order90_C9 × order90_C5) :=
  prodTrivialAction (A := order90_C9) (B := order90_C5) (H := order90_C2)
    (invActionHom order90_C5)

noncomputable abbrev order90_c5c9Action_26 :
    order90_C2 →* MulAut (order90_C5 × order90_C9) :=
  prodTrivialAction (A := order90_C5) (B := order90_C9) (H := order90_C2)
    (invActionHom order90_C9)

theorem order90_c45Action_19_crt :
    ∀ h, order90_c45_crt_iso_9_5.toMonoidHom.comp
        (order90_c45Action_19 h).toMonoidHom =
      (order90_c9c5Action_19 h).toMonoidHom.comp order90_c45_crt_iso_9_5.toMonoidHom := by
  intro h
  apply MonoidHom.ext
  intro x
  ext <;> decide +revert

theorem order90_c45Action_26_crt :
    ∀ h, order90_c45_crt_iso_5_9.toMonoidHom.comp
        (order90_c45Action_26 h).toMonoidHom =
      (order90_c5c9Action_26 h).toMonoidHom.comp order90_c45_crt_iso_5_9.toMonoidHom := by
  intro h
  apply MonoidHom.ext
  intro x
  ext <;> decide +revert

theorem order90_c45_19_semidirect_iso :
    Nonempty (SemidirectProduct order90_C45 order90_C2
      order90_c45Action_19 ≃* order90_C9D5) := by
  haveI : NeZero 5 := ⟨by norm_num⟩
  exact ⟨(semidirectProductCongr order90_c45_crt_iso_9_5 (MulEquiv.refl order90_C2)
    order90_c45Action_19_crt).trans
      ((semidirectProdSplit (A := order90_C9) (B := order90_C5) (H := order90_C2)
        (invActionHom order90_C5)).trans
          (MulEquiv.prodCongr (MulEquiv.refl order90_C9) (genDihedralCyclicIso 5)))⟩

theorem order90_c45_26_semidirect_iso :
    Nonempty (SemidirectProduct order90_C45 order90_C2
      order90_c45Action_26 ≃* order90_C5D9) := by
  haveI : NeZero 9 := ⟨by norm_num⟩
  exact ⟨(semidirectProductCongr order90_c45_crt_iso_5_9 (MulEquiv.refl order90_C2)
    order90_c45Action_26_crt).trans
      ((semidirectProdSplit (A := order90_C5) (B := order90_C9) (H := order90_C2)
        (invActionHom order90_C9)).trans
          (MulEquiv.prodCongr (MulEquiv.refl order90_C5) (genDihedralCyclicIso 9)))⟩

theorem order90_c45_semidirect_cases (φ : order90_C2 →* MulAut order90_C45) :
    Nonempty (SemidirectProduct order90_C45 order90_C2 φ ≃* order90_C90) ∨
      Nonempty (SemidirectProduct order90_C45 order90_C2 φ ≃* order90_C9D5) ∨
      Nonempty (SemidirectProduct order90_C45 order90_C2 φ ≃* order90_C5D9) ∨
      Nonempty (SemidirectProduct order90_C45 order90_C2 φ ≃* order90_D45) := by
  rcases order90_c45_action_cases φ with hφ | hφ | hφ | hφ
  · subst hφ
    exact Or.inl order90_c45_trivial_action_semidirect_iso
  · subst hφ
    exact Or.inr (Or.inl order90_c45_19_semidirect_iso)
  · subst hφ
    exact Or.inr (Or.inr (Or.inl order90_c45_26_semidirect_iso))
  · subst hφ
    exact Or.inr (Or.inr (Or.inr order90_c45_inv_semidirect_iso))

/-! ### The noncyclic abelian order-45 kernel -/

noncomputable def order90_psqPrimeRep2_iso : psqPrimeRep2 3 5 ≃* order90_E33C5 := by
  have hcop : (3 : ℕ).Coprime 5 := by norm_num
  exact (MulEquiv.prodCongr (MulEquiv.refl order90_C3) (crtProd 3 5 hcop).symm).trans
    (MulEquiv.prodAssoc (M := order90_C3) (N := order90_C3) (P := order90_C5)).symm

theorem order90_e33c5_pow_fifteen (x : order90_E33C5) : x ^ 15 = 1 := by
  decide +revert

noncomputable def order90_e33c5_decomp_semidirect
    (φ : order90_C2 →* MulAut order90_E33C5) :
    SemidirectProduct order90_E33C5 order90_C2 φ ≃*
      fixSubgroup (φ (Multiplicative.ofAdd 1)) ×
        SemidirectProduct (negSubgroup (φ (Multiplicative.ofAdd 1))) order90_C2
          (invActionHom (negSubgroup (φ (Multiplicative.ofAdd 1)))) := by
  let τ := φ (Multiplicative.ofAdd 1)
  have h2 : τ * τ = 1 := by
    rw [← sq, ← map_pow, show (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 from by decide,
      map_one]
  have hinv : ∀ x, τ (τ x) = x := fun x => by
    have hx := DFunLike.congr_fun h2 x
    rwa [MulAut.mul_apply, MulAut.one_apply] at hx
  have hexp : ∀ x : order90_E33C5, x ^ 15 = 1 := order90_e33c5_pow_fifteen
  have ht : 2 * 8 = 15 + 1 := by norm_num
  exact elem_decomp_semidirect (p := 15) (t := 8) hinv hexp ht φ rfl

private lemma order90_sign_mulLeft_of_orderOf_two [Fintype G] [DecidableEq G]
    (a : G) (ha : orderOf a = 2) (hcard : Odd (Nat.card G / 2)) :
    Equiv.Perm.sign (Equiv.mulLeft a) = -1 := by
  classical
  have ha2 : a ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ha]
  have hperm2 : (Equiv.mulLeft a : Equiv.Perm G) ^ 2 = 1 := by
    ext x
    change a * (a * x) = x
    rw [← mul_assoc, ← pow_two, ha2, one_mul]
  rw [Equiv.Perm.sign_of_pow_two_eq_one hperm2]
  have hfixed : Fintype.card (Function.fixedPoints (Equiv.mulLeft a : Equiv.Perm G)) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨x, hx⟩
    have : a * x = x := hx
    have ha1 : a = 1 := by
      simpa using congr_arg (fun y => y * x⁻¹) this
    have : orderOf a = 1 := by simp [ha1]
    omega
  rw [hfixed, tsub_zero]
  rw [Nat.card_eq_fintype_card] at hcard
  exact hcard.neg_one_pow

/-- Every group of order `90` has a normal subgroup of order `45`. -/
theorem order90_normal_45_subgroup [Finite G] (hG : Nat.card G = 90) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 45 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  let χ : G →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom G G)
  have hGft : Fintype.card G = 90 := by
    simpa [Nat.card_eq_fintype_card] using hG
  have hhalf : Nat.card G / 2 = 45 := by
    rw [Nat.card_eq_fintype_card, hGft]
  have hhalfodd : Odd (Nat.card G / 2) := by
    rw [hhalf]
    exact ⟨22, by norm_num⟩
  have htwo_dvd : 2 ∣ Nat.card G := by
    rw [hG]
    norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 htwo_dvd
  have hχa : χ a = -1 := by
    change Equiv.Perm.sign (MulAction.toPermHom G G a) = -1
    have hperm : MulAction.toPermHom G G a = Equiv.mulLeft a := by
      ext x
      rfl
    rw [hperm]
    exact order90_sign_mulLeft_of_orderOf_two a ha hhalfodd
  have hχsurj : Function.Surjective χ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one χ⟩
    · exact ⟨a, hχa⟩
  have hindex : χ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective χ hχsurj]
    simp [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hNcard : Nat.card χ.ker = 45 := by
    have hmul : Nat.card χ.ker * 2 = Nat.card G := by
      simpa [hindex] using χ.ker.card_mul_index
    apply Nat.mul_right_cancel (m := 2) (by norm_num : 0 < 2)
    rw [hmul, hG]
  exact ⟨χ.ker, inferInstance, hNcard⟩

/-- Every group of order `90` is a semidirect product of a normal group of order `45`
by a complement of order `2`. -/
theorem order90_semidirect [Finite G] (hG : Nat.card G = 90) :
    ∃ (N : Subgroup G) (_ : N.Normal) (_ : Nat.card N = 45)
      (K : Subgroup G) (φ : K →* MulAut N),
      Nonempty (G ≃* SemidirectProduct N K φ) := by
  obtain ⟨N, hNnormal, hNcard⟩ := order90_normal_45_subgroup hG
  haveI : N.Normal := hNnormal
  have hcop : Nat.Coprime 45 2 := by norm_num
  have hcard : Nat.card G = 45 * 2 := by
    norm_num [hG]
  obtain ⟨K, φ, hiso⟩ := schurZassenhaus_of_card hcard hcop N hNcard
  exact ⟨N, hNnormal, hNcard, K, φ, hiso⟩

/-- The index-two kernel in the order-`90` split is one of the two groups of order `45`. -/
theorem order90_semidirect_kernel_cases [Finite G] (hG : Nat.card G = 90) :
    ∃ (N : Subgroup G) (_ : N.Normal) (_ : Nat.card N = 45)
      (K : Subgroup G) (φ : K →* MulAut N),
      Nonempty (G ≃* SemidirectProduct N K φ) ∧
        (Nonempty (N ≃* psqPrimeRep1 3 5) ∨ Nonempty (N ≃* psqPrimeRep2 3 5)) := by
  obtain ⟨N, hNnormal, hNcard, K, φ, hiso⟩ := order90_semidirect hG
  haveI : Finite N := inferInstance
  have hNcard' : Nat.card N = 3 ^ 2 * 5 := by
    rw [hNcard]
    norm_num
  have hcases :
      Nonempty (N ≃* psqPrimeRep1 3 5) ∨ Nonempty (N ≃* psqPrimeRep2 3 5) :=
    psq_prime_abelian_classification (G := N) (p := 3) (q := 5) (by norm_num)
      (by norm_num) (by norm_num) (by decide) (by decide) hNcard'
  exact ⟨N, hNnormal, hNcard, K, φ, hiso, hcases⟩

end Smallgroups.UsefulTheorems
