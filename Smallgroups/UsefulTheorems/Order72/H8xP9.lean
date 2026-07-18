/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.P3Group
import Smallgroups.UsefulTheorems.PrimePairNonabelian
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.PGroupGeneration.Reconstruction
import Smallgroups.UsefulTheorems.SchurZassenhaus
import Smallgroups.UsefulTheorems.SemidirectProductClassify
import Smallgroups.UsefulTheorems.Order72.Sylow
import Mathlib.Data.ZMod.Aut
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.GroupTheory.PGroup

/-!
# Groups of order 72: the Sylow-2-normal branch (`H ⋊ P`, `H` order `8`, `P` order `9`)

If `G` has order `72` and its Sylow-`2` subgroup `H` (order `8`) is normal, Schur–Zassenhaus
gives `G ≃* H ⋊[φ] P` for `P` a complement of order `9`. `H` is one of the five order-`8`
types (`P3Group`), and `P` is one of the two order-`9` types (`prime_sq_classification`).

Since `|P| = 9 = 3²`, the action `φ : P →* MulAut H` always has image a finite `3`-group.
For three of the five `H`-types, `Nat.card (MulAut H)` is coprime to `3`, forcing `φ` to be
**trivial** regardless of which of the two `P`-types is used — so those combinations only
contribute the direct product `H × P`:

* `H = CyclicP3 2 ≃ ZMod 8`: `Nat.card (MulAut H) = φ(8) = 4` (via `ZMod.AddAutEquivUnits`
  and `MulAutMultiplicative`).
* `H = AbelianP2P 2 ≃ ZMod 4 × ZMod 2`, `H = DihedralGroup 4`: `Nat.card (MulAut H) = 8`.

The remaining two `H`-types, `QuaternionGroup 2` (`Aut ≅ S₄`, order `24`) and
`ElementaryP3 2 ≃ (ZMod 2)³` (`Aut ≅ GL(3,2)`, order `168`), genuinely admit order-`3`
automorphisms.  This file now builds standard representatives (`q8Cyc`, `e8Rot`) and proves the
needed order-`3` conjugacy classification for both targets, together with action-level helpers
for homomorphisms from a group of order `9`.

For `AbelianP2P 2` and `DihedralGroup 4`, `Nat.card (MulAut H)` isn't cheaply computable
(no totient-style formula, and brute-force search over `Equiv.Perm H` is too expensive), so
instead we directly prove "no automorphism of order `3`" by tracking a single generator's
orbit through `f` via `f³ = 1` (see `card_mulAut_abelianP2P_two_no_order_three` and
`card_mulAut_dihedralGroup_four_no_order_three`) — no permutation search involved.
-/

namespace Smallgroups.UsefulTheorems

open P3Group

/-! ### A general helper: a hom from a group of order `9` into an `Aut` group whose order is
coprime to `3` is trivial. -/

theorem mulAut_hom_trivial_of_not_three_dvd {H K : Type*} [Group H] [Group K] [Finite K]
    [Finite (MulAut H)] (hK : Nat.card K = 9)
    (hcop : ¬ (3 : ℕ) ∣ Nat.card (MulAut H)) (φ : K →* MulAut H) (k : K) : φ k = 1 := by
  have hordK : orderOf k ∣ 9 := hK ▸ orderOf_dvd_natCard k
  have hdvd1 : orderOf (φ k) ∣ orderOf k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
  have hdvd9 : orderOf (φ k) ∣ 9 := hdvd1.trans hordK
  have hdvdA : orderOf (φ k) ∣ Nat.card (MulAut H) := orderOf_dvd_natCard _
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9] at hdvd9
  obtain ⟨j, hj2, hje⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd9
  interval_cases j
  · rw [pow_zero] at hje; exact orderOf_eq_one_iff.mp hje
  · exfalso; apply hcop
    rw [pow_one] at hje
    exact hje ▸ hdvdA
  · exfalso; apply hcop
    have h3d9 : (3 : ℕ) ∣ 3 ^ 2 := ⟨3, by norm_num⟩
    exact (hje ▸ h3d9).trans hdvdA

/-! ### `Nat.card (MulAut H)` for the "easy" `H`-types. -/

/-- `Aut(ℤ/n)` has order `φ(n)` (Euler's totient). -/
theorem card_mulAut_multiplicative_zmod (n : ℕ) [NeZero n] :
    Nat.card (MulAut (Multiplicative (ZMod n))) = n.totient := by
  have h1 : Nat.card (MulAut (Multiplicative (ZMod n))) = Nat.card (AddAut (ZMod n)) :=
    Nat.card_congr (MulAutMultiplicative (G := ZMod n)).toEquiv
  have h2 : Nat.card (AddAut (ZMod n)) = Nat.card (ZMod n)ˣ :=
    Nat.card_congr (ZMod.AddAutEquivUnits n).toEquiv
  rw [h1, h2, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

theorem card_mulAut_cyclicP3_two : Nat.card (MulAut (Multiplicative (ZMod 8))) = 4 := by
  rw [card_mulAut_multiplicative_zmod]; decide

theorem card_mulAut_cyclicRep_nine : Nat.card (MulAut (CyclicRep 9)) = 6 := by
  rw [card_mulAut_multiplicative_zmod]
  decide

theorem order72_c9_action_value_sq_of_card_eight {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 8) (φ : K →* MulAut (CyclicRep 9)) (k : K) :
    (φ k) ^ 2 = 1 := by
  have hordK : orderOf k ∣ 8 := hK ▸ orderOf_dvd_natCard k
  have hdvd1 : orderOf (φ k) ∣ orderOf k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, pow_orderOf_eq_one, map_one])
  have hdvd8 : orderOf (φ k) ∣ 8 := hdvd1.trans hordK
  have hdvd6 : orderOf (φ k) ∣ 6 := by
    rw [← card_mulAut_cyclicRep_nine]
    exact orderOf_dvd_natCard (φ k)
  have hdvd2 : orderOf (φ k) ∣ 2 := by
    have h := Nat.dvd_gcd hdvd8 hdvd6
    simpa using h
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd2

theorem order72_c9_action_value_one_or_order_two_of_card_eight {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 8) (φ : K →* MulAut (CyclicRep 9)) (k : K) :
    φ k = 1 ∨ orderOf (φ k) = 2 := by
  by_cases h : φ k = 1
  · exact Or.inl h
  · exact Or.inr (orderOf_eq_prime (order72_c9_action_value_sq_of_card_eight hK φ k) h)

noncomputable abbrev order72_c9InvAut : MulAut (CyclicRep 9) :=
  unitAutHom (-1 : (ZMod 9)ˣ)

theorem order72_unitAutHom_c9_injective : Function.Injective (unitAutHom (p := 9)) := by
  intro u v h
  have h1 : unitAutHom u (Multiplicative.ofAdd (1 : ZMod 9)) =
      unitAutHom v (Multiplicative.ofAdd (1 : ZMod 9)) := by rw [h]
  simp only [unitAutHom_apply, mul_one, EmbeddingLike.apply_eq_iff_eq] at h1
  exact Units.ext (congrArg Multiplicative.toAdd h1)

theorem order72_mulAut_c9_eq_unitAutHom (σ : MulAut (CyclicRep 9)) :
    ∃ u : (ZMod 9)ˣ, σ = unitAutHom u := by
  let f : AddAut (ZMod 9) := Multiplicative.toAdd ((MulAutMultiplicative (ZMod 9)) σ)
  let u : (ZMod 9)ˣ := Additive.toMul ((ZMod.AddAutEquivUnits 9) f)
  refine ⟨u, ?_⟩
  ext x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  change Multiplicative.ofAdd (f m) = unitAutHom u (Multiplicative.ofAdd m)
  have hu : Additive.ofMul u = (ZMod.AddAutEquivUnits 9) f := by simp [u]
  have hf : f = (ZMod.AddAutEquivUnits 9).symm (Additive.ofMul u) := by
    symm
    rw [hu]
    exact AddEquiv.symm_apply_apply (ZMod.AddAutEquivUnits 9) f
  rw [hf, unitAutHom_apply]
  simp [ZMod.AddAutEquivUnits_symm_apply, Units.smul_def]

theorem order72_zmod9_unit_sq_eq_one_cases (u : (ZMod 9)ˣ) (_hu : u ^ 2 = 1) :
    u = 1 ∨ u = -1 := by
  revert u
  decide

theorem order72_mulAut_c9_sq_eq_one_cases (σ : MulAut (CyclicRep 9)) (hσ : σ ^ 2 = 1) :
    σ = 1 ∨ σ = order72_c9InvAut := by
  obtain ⟨u, hu⟩ := order72_mulAut_c9_eq_unitAutHom σ
  have hu2 : u ^ 2 = 1 := by
    apply order72_unitAutHom_c9_injective
    rw [map_pow, ← hu, hσ, map_one]
  rcases order72_zmod9_unit_sq_eq_one_cases u hu2 with hu1 | huneg
  · left
    rw [hu, hu1, map_one]
  · right
    rw [hu, huneg, order72_c9InvAut]

theorem order72_c9_action_value_one_or_inv_of_card_eight {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 8) (φ : K →* MulAut (CyclicRep 9)) (k : K) :
    φ k = 1 ∨ φ k = order72_c9InvAut :=
  order72_mulAut_c9_sq_eq_one_cases (φ k) (order72_c9_action_value_sq_of_card_eight hK φ k)

/-! ### A second helper: trivial action from "no order-`3` automorphism" directly (avoids
needing `Nat.card (MulAut H)` at all — useful when that cardinality isn't cheaply
computable). -/

theorem mulAut_hom_trivial_of_no_order_three {H K : Type*} [Group H] [Group K] [Finite K]
    (hK : Nat.card K = 9) (hno3 : ∀ f : MulAut H, f ^ 3 = 1 → f = 1)
    (φ : K →* MulAut H) (k : K) : φ k = 1 := by
  have hordK : orderOf k ∣ 9 := hK ▸ orderOf_dvd_natCard k
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9] at hordK
  obtain ⟨j, hj2, hje⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hordK
  have hk3j : k ^ (3 ^ j) = 1 := hje ▸ pow_orderOf_eq_one k
  have hφ : (φ k) ^ (3 ^ j) = 1 := by rw [← map_pow, hk3j, map_one]
  interval_cases j
  · simpa using hφ
  · exact hno3 (φ k) (by simpa using hφ)
  · have h1 : (φ k) ^ 3 = 1 :=
      hno3 ((φ k) ^ 3) (by rw [← pow_mul]; norm_num at hφ ⊢; exact hφ)
    exact hno3 (φ k) h1

/-- A nontrivial homomorphism has a nontrivial value.  This small helper keeps later
`Aut`-valued action arguments from invoking recursive `ext` search. -/
private theorem exists_apply_ne_one_of_monoidHom_ne_one {K A : Type*} [Group K] [Group A]
    (φ : K →* A) (hφ : φ ≠ 1) : ∃ k : K, φ k ≠ 1 := by
  by_contra h
  apply hφ
  apply MonoidHom.ext
  intro k
  by_contra hk
  exact h ⟨k, hk⟩

/-- The cyclic-source homomorphism sending the additive generator of `ZMod n` to an element
whose `n`-th power is trivial. -/
noncomputable def zmodActionHom {A : Type*} [Group A] (n : ℕ) [NeZero n]
    (a : A) (ha : a ^ n = 1) : CyclicRep n →* A :=
  zmodZPowHom n a ha

@[simp] theorem zmodActionHom_gen {A : Type*} [Group A] (n : ℕ) [NeZero n]
    (a : A) (ha : a ^ n = 1) :
    zmodActionHom n a ha (Multiplicative.ofAdd (1 : ZMod n)) = a := by
  simpa [zmodActionHom] using zmodZPowHom_intCast n a ha (1 : ℤ)

/-- Homomorphisms out of `CyclicRep n` are determined by the additive generator `1`. -/
theorem cyclicRep_hom_ext {n : ℕ} [NeZero n] {M : Type*} [Monoid M]
    {φ ψ : CyclicRep n →* M}
    (hgen : φ (Multiplicative.ofAdd (1 : ZMod n)) =
      ψ (Multiplicative.ofAdd (1 : ZMod n))) :
    φ = ψ := by
  apply MonoidHom.ext
  intro x
  let k : ZMod n := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod n)) ^ k.val := by
    rw [show x = Multiplicative.ofAdd k from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd k = Multiplicative.ofAdd ((k.val : ZMod n)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (k.val • (1 : ZMod n)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod n)) ^ k.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, hgen]

theorem order72_c9InvAut_sq : order72_c9InvAut ^ 2 = 1 := by
  rw [order72_c9InvAut, ← map_pow (unitAutHom (p := 9))]
  norm_num

noncomputable def order72_c9C8InvAction :
    Multiplicative (ZMod 8) →* MulAut (CyclicRep 9) :=
  zmodActionHom 8 order72_c9InvAut (by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, order72_c9InvAut_sq, one_pow])

@[simp] theorem order72_c9C8InvAction_gen :
    order72_c9C8InvAction (Multiplicative.ofAdd (1 : ZMod 8)) = order72_c9InvAut := by
  rw [order72_c9C8InvAction, zmodActionHom_gen]

abbrev order72_C9_C8_inv : Type :=
  SemidirectProduct (CyclicRep 9) (Multiplicative (ZMod 8)) order72_c9C8InvAction

theorem order72_c9_c8_action_cases
    (φ : Multiplicative (ZMod 8) →* MulAut (CyclicRep 9)) :
    φ = 1 ∨ φ = order72_c9C8InvAction := by
  let g : Multiplicative (ZMod 8) := Multiplicative.ofAdd (1 : ZMod 8)
  have hcard : Nat.card (Multiplicative (ZMod 8)) = 8 :=
    card_cyclicRep (by norm_num : (8 : ℕ) ≠ 0)
  rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ g with h | h
  · left
    apply cyclicRep_hom_ext
    simp [g, h]
  · right
    apply cyclicRep_hom_ext
    rw [h, order72_c9C8InvAction_gen]

theorem order72_c9_c8_semidirect_cases
    (φ : Multiplicative (ZMod 8) →* MulAut (CyclicRep 9)) :
    Nonempty (SemidirectProduct (CyclicRep 9) (Multiplicative (ZMod 8)) φ ≃*
      CyclicRep 9 × Multiplicative (ZMod 8)) ∨
    Nonempty (SemidirectProduct (CyclicRep 9) (Multiplicative (ZMod 8)) φ ≃*
      order72_C9_C8_inv) := by
  rcases order72_c9_c8_action_cases φ with hφ | hφ
  · exact Or.inl ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · exact Or.inr ⟨semidirectProductCongr_eq hφ⟩

theorem order72_c9_c8_branch_cases {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (CyclicRep 9)}
    (e : G ≃* SemidirectProduct (CyclicRep 9) (Multiplicative (ZMod 8)) φ) :
    Nonempty (G ≃* CyclicRep 9 × Multiplicative (ZMod 8)) ∨
    Nonempty (G ≃* order72_C9_C8_inv) := by
  rcases order72_c9_c8_semidirect_cases φ with h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr ⟨e.trans eh⟩

/-- The first standard generator of `C3 × C3`. -/
abbrev order72_E9_g1 : ElemAbelianRep 3 := (Multiplicative.ofAdd (1 : ZMod 3), 1)

/-- The second standard generator of `C3 × C3`. -/
abbrev order72_E9_g2 : ElemAbelianRep 3 := (1, Multiplicative.ofAdd (1 : ZMod 3))

/-- Homomorphisms out of `C3 × C3` are determined by the two standard generators. -/
theorem elemAbelianRep3_hom_ext {M : Type*} [Monoid M] {φ ψ : ElemAbelianRep 3 →* M}
    (h1 : φ order72_E9_g1 = ψ order72_E9_g1)
    (h2 : φ order72_E9_g2 = ψ order72_E9_g2) : φ = ψ := by
  apply MonoidHom.ext
  intro x
  obtain ⟨x1, x2⟩ := x
  have hdecomp : ((x1, x2) : ElemAbelianRep 3) = (x1, 1) * (1, x2) := by
    ext <;> simp
  rw [hdecomp, map_mul, map_mul]
  congr 1
  · let j : ZMod 3 := Multiplicative.toAdd x1
    have hx0 : Multiplicative.ofAdd j = x1 := ofAdd_toAdd x1
    rw [← hx0]
    have hp : ((Multiplicative.ofAdd j, 1) : ElemAbelianRep 3) = order72_E9_g1 ^ j.val := by
      ext
      · simp only [order72_E9_g1, Prod.pow_fst]
        rw [← ofAdd_nsmul]
        simp
      · simp [order72_E9_g1]
    rw [hp, map_pow, map_pow, h1]
  · let j : ZMod 3 := Multiplicative.toAdd x2
    have hx0 : Multiplicative.ofAdd j = x2 := ofAdd_toAdd x2
    rw [← hx0]
    have hp : ((1, Multiplicative.ofAdd j) : ElemAbelianRep 3) = order72_E9_g2 ^ j.val := by
      ext
      · simp [order72_E9_g2]
      · simp only [order72_E9_g2, Prod.pow_snd]
        rw [← ofAdd_nsmul]
        simp
    rw [hp, map_pow, map_pow, h2]

/-- Automorphisms of `C3 × C3` are determined by the two standard generators. -/
theorem order72_E9_aut_ext {σ τ : MulAut (ElemAbelianRep 3)}
    (h1 : σ order72_E9_g1 = τ order72_E9_g1)
    (h2 : σ order72_E9_g2 = τ order72_E9_g2) : σ = τ := by
  have hhom : σ.toMonoidHom = τ.toMonoidHom := elemAbelianRep3_hom_ext h1 h2
  apply MulEquiv.ext
  intro x
  exact congrArg (fun f : ElemAbelianRep 3 →* ElemAbelianRep 3 => f x) hhom

def order72_E9_coord (x : ElemAbelianRep 3) : Nat × Nat :=
  ((Multiplicative.toAdd x.1).val, (Multiplicative.toAdd x.2).val)

theorem order72_E9_coord_injective : Function.Injective order72_E9_coord := by
  intro x y h
  revert x y
  decide

def order72_E9_autCode (σ : MulAut (ElemAbelianRep 3)) :
    (Nat × Nat) × (Nat × Nat) :=
  (order72_E9_coord (σ order72_E9_g1), order72_E9_coord (σ order72_E9_g2))

theorem order72_E9_autCode_injective : Function.Injective order72_E9_autCode := by
  intro σ τ h
  apply order72_E9_aut_ext
  · exact order72_E9_coord_injective (congrArg Prod.fst h)
  · exact order72_E9_coord_injective (congrArg Prod.snd h)

/-- The nontrivial automorphism of `C3`, written multiplicatively as squaring. -/
noncomputable def order72_C3_squareAut : CyclicRep 3 ≃* CyclicRep 3 where
  toFun x := x ^ 2
  invFun x := x ^ 2
  left_inv x := by decide +revert
  right_inv x := by decide +revert
  map_mul' x y := by decide +revert

/-- Multiply the first `C3` coordinate by `2`. -/
noncomputable def order72_E9_scaleFirst2 : ElemAbelianRep 3 ≃* ElemAbelianRep 3 :=
  MulEquiv.prodCongr order72_C3_squareAut (MulEquiv.refl _)

/-- Multiply the second `C3` coordinate by `2`. -/
noncomputable def order72_E9_scaleSecond2 : ElemAbelianRep 3 ≃* ElemAbelianRep 3 :=
  MulEquiv.prodCongr (MulEquiv.refl _) order72_C3_squareAut

/-- Swap the two `C3` coordinates. -/
noncomputable def order72_E9_swap : ElemAbelianRep 3 ≃* ElemAbelianRep 3 where
  toFun x := (x.2, x.1)
  invFun x := (x.2, x.1)
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_mul' x y := by rfl

/-- The shear `(x, y) ↦ (xy, y)` of `C3 × C3`. -/
noncomputable def order72_E9_shearPlus : ElemAbelianRep 3 ≃* ElemAbelianRep 3 where
  toFun x := (x.1 * x.2, x.2)
  invFun x := (x.1 * x.2⁻¹, x.2)
  left_inv x := by ext <;> simp [mul_assoc]
  right_inv x := by ext <;> simp [mul_assoc]
  map_mul' x y := by ext <;> simp [mul_left_comm, mul_comm]

/-- The lower shear `(x, y) ↦ (x, xy)` of `C3 × C3`. -/
noncomputable def order72_E9_shearLower : ElemAbelianRep 3 ≃* ElemAbelianRep 3 where
  toFun x := (x.1, x.1 * x.2)
  invFun x := (x.1, x.1⁻¹ * x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by ext <;> simp [mul_left_comm, mul_comm]

theorem order72_E9_scaleFirst2_g1 :
    order72_E9_scaleFirst2 order72_E9_g1 = order72_E9_g1 ^ 2 := by
  decide

theorem order72_E9_scaleFirst2_g2 : order72_E9_scaleFirst2 order72_E9_g2 = order72_E9_g2 := by
  decide

theorem order72_E9_scaleSecond2_g1 : order72_E9_scaleSecond2 order72_E9_g1 = order72_E9_g1 := by
  decide

theorem order72_E9_scaleSecond2_g2 :
    order72_E9_scaleSecond2 order72_E9_g2 = order72_E9_g2 ^ 2 := by
  decide

theorem order72_E9_swap_g1 : order72_E9_swap order72_E9_g1 = order72_E9_g2 := rfl

theorem order72_E9_swap_g2 : order72_E9_swap order72_E9_g2 = order72_E9_g1 := rfl

theorem order72_E9_shearPlus_g1 : order72_E9_shearPlus order72_E9_g1 = order72_E9_g1 := by
  ext <;> simp [order72_E9_shearPlus, order72_E9_g1]

theorem order72_E9_shearPlus_g2 :
    order72_E9_shearPlus order72_E9_g2 = order72_E9_g1 * order72_E9_g2 := by
  ext <;> simp [order72_E9_shearPlus, order72_E9_g1, order72_E9_g2]

theorem order72_E9_shearLower_g1 :
    order72_E9_shearLower order72_E9_g1 = order72_E9_g1 * order72_E9_g2 := by
  ext <;> simp [order72_E9_shearLower, order72_E9_g1, order72_E9_g2]

theorem order72_E9_shearLower_g2 :
    order72_E9_shearLower order72_E9_g2 = order72_E9_g2 := by
  ext <;> simp [order72_E9_shearLower, order72_E9_g2]

theorem order72_E9_shearMinus_g1 : order72_E9_shearPlus.symm order72_E9_g1 = order72_E9_g1 := by
  ext <;> simp [order72_E9_shearPlus, order72_E9_g1]

theorem order72_E9_shearMinus_g2 :
    order72_E9_shearPlus.symm order72_E9_g2 = order72_E9_g1 ^ 2 * order72_E9_g2 := by
  ext
  · change -(1 : ZMod 3) = 2
    decide
  · rfl

/-- The change of basis with columns `g₁g₂²` and `g₁g₂`, used to conjugate the
standard reflection to the coordinate swap. -/
noncomputable def order72_E9_swapReflectBasis : ElemAbelianRep 3 ≃* ElemAbelianRep 3 where
  toFun x := (x.1 * x.2, x.1 ^ 2 * x.2)
  invFun x := (x.1 ^ 2 * x.2, x.1 ^ 2 * x.2 ^ 2)
  left_inv x := by decide +revert
  right_inv x := by decide +revert
  map_mul' x y := by ext <;> simp [mul_left_comm, mul_comm, pow_succ]

/-- The central involution `-I` on `C3 × C3`. -/
noncomputable def order72_E9_negAut : MulAut (ElemAbelianRep 3) :=
  order72_E9_scaleFirst2.trans order72_E9_scaleSecond2

/-- A noncentral involution on `C3 × C3`, represented by `diag(-1, 1)`. -/
noncomputable abbrev order72_E9_reflectAut : MulAut (ElemAbelianRep 3) :=
  order72_E9_scaleFirst2

/-- A standard order-`4` element of `GL(2,3)`, sending `g₁ ↦ g₂`, `g₂ ↦ g₁²`. -/
noncomputable def order72_E9_order4Aut : MulAut (ElemAbelianRep 3) :=
  order72_E9_swap.trans order72_E9_scaleFirst2

/-- A standard order-`8` element of `GL(2,3)`, sending `g₁ ↦ g₁g₂`, `g₂ ↦ g₁`. -/
noncomputable def order72_E9_order8Aut : MulAut (ElemAbelianRep 3) :=
  order72_E9_swap.trans order72_E9_shearPlus

@[simp] theorem order72_E9_negAut_g1 :
    order72_E9_negAut order72_E9_g1 = order72_E9_g1 ^ 2 := by
  decide

@[simp] theorem order72_E9_negAut_g2 :
    order72_E9_negAut order72_E9_g2 = order72_E9_g2 ^ 2 := by
  decide

@[simp] theorem order72_E9_reflectAut_g1 :
    order72_E9_reflectAut order72_E9_g1 = order72_E9_g1 ^ 2 :=
  order72_E9_scaleFirst2_g1

@[simp] theorem order72_E9_reflectAut_g2 :
    order72_E9_reflectAut order72_E9_g2 = order72_E9_g2 :=
  order72_E9_scaleFirst2_g2

@[simp] theorem order72_E9_order4Aut_g1 :
    order72_E9_order4Aut order72_E9_g1 = order72_E9_g2 := by
  rfl

@[simp] theorem order72_E9_order4Aut_g2 :
    order72_E9_order4Aut order72_E9_g2 = order72_E9_g1 ^ 2 := by
  decide

@[simp] theorem order72_E9_order8Aut_g1 :
    order72_E9_order8Aut order72_E9_g1 = order72_E9_g1 * order72_E9_g2 := by
  rfl

@[simp] theorem order72_E9_order8Aut_g2 :
    order72_E9_order8Aut order72_E9_g2 = order72_E9_g1 := by
  rfl

theorem order72_E9_negAut_sq : order72_E9_negAut ^ 2 = 1 := by
  apply order72_E9_aut_ext <;> decide

theorem order72_E9_reflectAut_sq : order72_E9_reflectAut ^ 2 = 1 := by
  apply order72_E9_aut_ext <;> decide

theorem order72_E9_order4Aut_pow4 : order72_E9_order4Aut ^ 4 = 1 := by
  apply order72_E9_aut_ext <;> decide

theorem order72_E9_order8Aut_pow8 : order72_E9_order8Aut ^ 8 = 1 := by
  apply order72_E9_aut_ext <;> decide

private noncomputable def order72_E9_reflectLowerShear : MulAut (ElemAbelianRep 3) :=
  (MulAut.conj order72_E9_shearLower) order72_E9_reflectAut

theorem order72_E9_reflectLowerShear_code :
    order72_E9_autCode order72_E9_reflectLowerShear = ((2, 1), (0, 1)) := by
  decide

theorem order72_E9_reflectLowerShear_conj_code :
    order72_E9_autCode
        ((MulAut.conj order72_E9_shearLower.symm) order72_E9_reflectLowerShear) =
      order72_E9_autCode order72_E9_reflectAut := by
  decide

private noncomputable def order72_E9_reflectLowerShearSq : MulAut (ElemAbelianRep 3) :=
  (MulAut.conj (order72_E9_shearLower ^ 2)) order72_E9_reflectAut

theorem order72_E9_reflectLowerShearSq_code :
    order72_E9_autCode order72_E9_reflectLowerShearSq = ((2, 2), (0, 1)) := by
  decide

theorem order72_E9_reflectLowerShearSq_conj_code :
    order72_E9_autCode
        ((MulAut.conj ((order72_E9_shearLower ^ 2).symm))
          order72_E9_reflectLowerShearSq) =
      order72_E9_autCode order72_E9_reflectAut := by
  decide

private noncomputable def order72_E9_reflectSecond : MulAut (ElemAbelianRep 3) :=
  (MulAut.conj order72_E9_swap) order72_E9_reflectAut

theorem order72_E9_reflectSecond_code :
    order72_E9_autCode order72_E9_reflectSecond = ((1, 0), (0, 2)) := by
  decide

theorem order72_E9_reflectSecond_conj_code :
    order72_E9_autCode ((MulAut.conj order72_E9_swap) order72_E9_reflectSecond) =
      order72_E9_autCode order72_E9_reflectAut := by
  decide

private noncomputable def order72_E9_reflectSecondShearInv : MulAut (ElemAbelianRep 3) :=
  (MulAut.conj order72_E9_shearLower.symm) order72_E9_reflectSecond

theorem order72_E9_reflectSecondShearInv_code :
    order72_E9_autCode order72_E9_reflectSecondShearInv = ((1, 1), (0, 2)) := by
  decide

theorem order72_E9_reflectSecondShearInv_conj_code :
    order72_E9_autCode
        ((MulAut.conj (order72_E9_shearLower.trans order72_E9_swap))
          order72_E9_reflectSecondShearInv) =
      order72_E9_autCode order72_E9_reflectAut := by
  decide

private noncomputable def order72_E9_reflectSecondShear : MulAut (ElemAbelianRep 3) :=
  (MulAut.conj order72_E9_shearLower) order72_E9_reflectSecond

theorem order72_E9_reflectSecondShear_code :
    order72_E9_autCode order72_E9_reflectSecondShear = ((1, 2), (0, 2)) := by
  decide

theorem order72_E9_reflectSecondShear_conj_code :
    order72_E9_autCode
        ((MulAut.conj (order72_E9_shearLower.symm.trans order72_E9_swap))
          order72_E9_reflectSecondShear) =
      order72_E9_autCode order72_E9_reflectAut := by
  decide

private noncomputable def order72_E9_reflectSwap : MulAut (ElemAbelianRep 3) :=
  (MulAut.conj order72_E9_swapReflectBasis) order72_E9_reflectAut

theorem order72_E9_reflectSwap_code :
    order72_E9_autCode order72_E9_reflectSwap = ((0, 1), (1, 0)) := by
  decide

theorem order72_E9_reflectSwap_conj_code :
    order72_E9_autCode
        ((MulAut.conj order72_E9_swapReflectBasis.symm) order72_E9_reflectSwap) =
      order72_E9_autCode order72_E9_reflectAut := by
  decide

private noncomputable def order72_E9_reflectSwapLowerShear : MulAut (ElemAbelianRep 3) :=
  (MulAut.conj order72_E9_shearLower) order72_E9_reflectSwap

theorem order72_E9_reflectSwapLowerShear_code :
    order72_E9_autCode order72_E9_reflectSwapLowerShear = ((2, 0), (1, 1)) := by
  decide

theorem order72_E9_reflectSwapLowerShear_conj_code :
    order72_E9_autCode
        ((MulAut.conj (order72_E9_shearLower.symm.trans order72_E9_swapReflectBasis.symm))
          order72_E9_reflectSwapLowerShear) =
      order72_E9_autCode order72_E9_reflectAut := by
  decide

private noncomputable def order72_E9_reflectSwapLowerShearSq : MulAut (ElemAbelianRep 3) :=
  (MulAut.conj (order72_E9_shearLower ^ 2)) order72_E9_reflectSwap

theorem order72_E9_reflectSwapLowerShearSq_code :
    order72_E9_autCode order72_E9_reflectSwapLowerShearSq = ((1, 0), (1, 2)) := by
  decide

theorem order72_E9_reflectSwapLowerShearSq_conj_code :
    order72_E9_autCode
        ((MulAut.conj (((order72_E9_shearLower ^ 2).symm).trans
          order72_E9_swapReflectBasis.symm)) order72_E9_reflectSwapLowerShearSq) =
      order72_E9_autCode order72_E9_reflectAut := by
  decide

private noncomputable def order72_E9_reflectUpperShear : MulAut (ElemAbelianRep 3) :=
  (MulAut.conj order72_E9_shearPlus) order72_E9_reflectAut

theorem order72_E9_reflectUpperShear_code :
    order72_E9_autCode order72_E9_reflectUpperShear = ((2, 0), (2, 1)) := by
  decide

theorem order72_E9_reflectUpperShear_conj_code :
    order72_E9_autCode
        ((MulAut.conj order72_E9_shearPlus.symm) order72_E9_reflectUpperShear) =
      order72_E9_autCode order72_E9_reflectAut := by
  decide

private noncomputable def order72_E9_reflectSecondUpperShearInv :
    MulAut (ElemAbelianRep 3) :=
  (MulAut.conj order72_E9_shearPlus.symm) order72_E9_reflectSecond

theorem order72_E9_reflectSecondUpperShearInv_code :
    order72_E9_autCode order72_E9_reflectSecondUpperShearInv = ((1, 0), (2, 2)) := by
  decide

theorem order72_E9_reflectSecondUpperShearInv_conj_code :
    order72_E9_autCode
        ((MulAut.conj (order72_E9_shearPlus.trans order72_E9_swap))
          order72_E9_reflectSecondUpperShearInv) =
      order72_E9_autCode order72_E9_reflectAut := by
  decide

/-- The change of basis with columns `g₁g₂` and `g₁g₂²`, used to conjugate the
standard reflection to the negative coordinate swap. -/
noncomputable def order72_E9_negSwapReflectBasis : ElemAbelianRep 3 ≃* ElemAbelianRep 3 where
  toFun x := (x.1 * x.2, x.1 * x.2 ^ 2)
  invFun x := (x.1 ^ 2 * x.2 ^ 2, x.1 ^ 2 * x.2)
  left_inv x := by decide +revert
  right_inv x := by decide +revert
  map_mul' x y := by ext <;> simp [mul_left_comm, mul_comm, pow_succ]

private noncomputable def order72_E9_reflectNegSwap : MulAut (ElemAbelianRep 3) :=
  (MulAut.conj order72_E9_negSwapReflectBasis) order72_E9_reflectAut

theorem order72_E9_reflectNegSwap_code :
    order72_E9_autCode order72_E9_reflectNegSwap = ((0, 2), (2, 0)) := by
  decide

theorem order72_E9_reflectNegSwap_conj_code :
    order72_E9_autCode
        ((MulAut.conj order72_E9_negSwapReflectBasis.symm) order72_E9_reflectNegSwap) =
      order72_E9_autCode order72_E9_reflectAut := by
  decide

theorem order72_E9_standard_odd_aut_codes :
    order72_E9_autCode (1 : MulAut (ElemAbelianRep 3)) = ((1, 0), (0, 1)) ∧
      order72_E9_autCode order72_E9_negAut = ((2, 0), (0, 2)) ∧
      order72_E9_autCode order72_E9_reflectAut = ((2, 0), (0, 1)) ∧
      order72_E9_autCode order72_E9_order4Aut = ((0, 1), (2, 0)) ∧
      order72_E9_autCode (order72_E9_order4Aut ^ 3) = ((0, 2), (1, 0)) ∧
      order72_E9_autCode order72_E9_order8Aut = ((1, 1), (1, 0)) ∧
      order72_E9_autCode (order72_E9_order8Aut ^ 3) = ((0, 2), (2, 1)) ∧
      order72_E9_autCode (order72_E9_order8Aut ^ 5) = ((2, 2), (2, 0)) ∧
      order72_E9_autCode (order72_E9_order8Aut ^ 7) = ((0, 1), (1, 2)) := by
  decide

noncomputable def order72_e9C8NegAction :
    Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3) :=
  zmodActionHom 8 order72_E9_negAut (by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, order72_E9_negAut_sq, one_pow])

noncomputable def order72_e9C8ReflectAction :
    Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3) :=
  zmodActionHom 8 order72_E9_reflectAut (by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, order72_E9_reflectAut_sq, one_pow])

noncomputable def order72_e9C8Order4Action :
    Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3) :=
  zmodActionHom 8 order72_E9_order4Aut (by
    rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, order72_E9_order4Aut_pow4, one_pow])

noncomputable def order72_e9C8Order8Action :
    Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3) :=
  zmodActionHom 8 order72_E9_order8Aut order72_E9_order8Aut_pow8

@[simp] theorem order72_e9C8NegAction_gen :
    order72_e9C8NegAction (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_negAut := by
  rw [order72_e9C8NegAction, zmodActionHom_gen]

@[simp] theorem order72_e9C8ReflectAction_gen :
    order72_e9C8ReflectAction (Multiplicative.ofAdd (1 : ZMod 8)) =
      order72_E9_reflectAut := by
  rw [order72_e9C8ReflectAction, zmodActionHom_gen]

@[simp] theorem order72_e9C8Order4Action_gen :
    order72_e9C8Order4Action (Multiplicative.ofAdd (1 : ZMod 8)) =
      order72_E9_order4Aut := by
  rw [order72_e9C8Order4Action, zmodActionHom_gen]

@[simp] theorem order72_e9C8Order8Action_gen :
    order72_e9C8Order8Action (Multiplicative.ofAdd (1 : ZMod 8)) =
      order72_E9_order8Aut := by
  rw [order72_e9C8Order8Action, zmodActionHom_gen]

abbrev order72_E9_C8_neg : Type :=
  SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) order72_e9C8NegAction

abbrev order72_E9_C8_reflect : Type :=
  SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8))
    order72_e9C8ReflectAction

abbrev order72_E9_C8_order4 : Type :=
  SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8))
    order72_e9C8Order4Action

abbrev order72_E9_C8_order8 : Type :=
  SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8))
    order72_e9C8Order8Action

theorem order72_e9_c8_action_eq_of_gen
    {φ ψ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (hgen : φ (Multiplicative.ofAdd (1 : ZMod 8)) =
      ψ (Multiplicative.ofAdd (1 : ZMod 8))) :
    φ = ψ :=
  cyclicRep_hom_ext hgen

theorem order72_e9_c8_action_gen_pow8
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)) :
    φ (Multiplicative.ofAdd (1 : ZMod 8)) ^ 8 = 1 := by
  have hg : (Multiplicative.ofAdd (1 : ZMod 8)) ^ 8 = 1 := by decide
  rw [← map_pow]
  rw [hg, map_one]

theorem order72_e9_c8_semidirect_case_of_gen_eq_one
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : φ (Multiplicative.ofAdd (1 : ZMod 8)) = 1) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      ElemAbelianRep 3 × Multiplicative (ZMod 8)) := by
  have h : φ = 1 := order72_e9_c8_action_eq_of_gen (by simp [hφ])
  exact ⟨(semidirectProductCongr_eq h).trans SemidirectProduct.mulEquivProd⟩

theorem order72_e9_c8_semidirect_case_of_gen_eq_neg
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_negAut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_neg) := by
  have h : φ = order72_e9C8NegAction := order72_e9_c8_action_eq_of_gen (by simp [hφ])
  exact ⟨semidirectProductCongr_eq h⟩

theorem order72_e9_c8_semidirect_case_of_gen_eq_reflect
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_reflectAut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  have h : φ = order72_e9C8ReflectAction :=
    order72_e9_c8_action_eq_of_gen (by simp [hφ])
  exact ⟨semidirectProductCongr_eq h⟩

theorem order72_e9_c8_semidirect_case_of_gen_eq_order4
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order4Aut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order4) := by
  have h : φ = order72_e9C8Order4Action :=
    order72_e9_c8_action_eq_of_gen (by simp [hφ])
  exact ⟨semidirectProductCongr_eq h⟩

theorem order72_e9_c8_semidirect_case_of_gen_eq_order8
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  have h : φ = order72_e9C8Order8Action :=
    order72_e9_c8_action_eq_of_gen (by simp [hφ])
  exact ⟨semidirectProductCongr_eq h⟩

private noncomputable def order72_C8_mulThree :
    Multiplicative (ZMod 8) ≃* Multiplicative (ZMod 8) :=
  unitAutHom (p := 8) (ZMod.unitOfCoprime 3 (by norm_num : Nat.Coprime 3 8))

private noncomputable def order72_C8_mulFive :
    Multiplicative (ZMod 8) ≃* Multiplicative (ZMod 8) :=
  unitAutHom (p := 8) (ZMod.unitOfCoprime 5 (by norm_num : Nat.Coprime 5 8))

private noncomputable def order72_C8_mulSeven :
    Multiplicative (ZMod 8) ≃* Multiplicative (ZMod 8) :=
  unitAutHom (p := 8) (ZMod.unitOfCoprime 7 (by norm_num : Nat.Coprime 7 8))

@[simp] private theorem order72_C8_mulThree_gen :
    order72_C8_mulThree (Multiplicative.ofAdd (1 : ZMod 8)) =
      (Multiplicative.ofAdd (1 : ZMod 8)) ^ 3 := by
  decide

@[simp] private theorem order72_C8_mulFive_gen :
    order72_C8_mulFive (Multiplicative.ofAdd (1 : ZMod 8)) =
      (Multiplicative.ofAdd (1 : ZMod 8)) ^ 5 := by
  decide

@[simp] private theorem order72_C8_mulSeven_gen :
    order72_C8_mulSeven (Multiplicative.ofAdd (1 : ZMod 8)) =
      (Multiplicative.ofAdd (1 : ZMod 8)) ^ 7 := by
  decide

theorem order72_e9_c8_semidirect_case_of_gen_eq_order4_pow3
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order4Aut ^ 3) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order4) := by
  have h : φ = order72_e9C8Order4Action.comp order72_C8_mulThree.toMonoidHom :=
    order72_e9_c8_action_eq_of_gen (by
      change φ (Multiplicative.ofAdd (1 : ZMod 8)) =
        order72_e9C8Order4Action (order72_C8_mulThree (Multiplicative.ofAdd (1 : ZMod 8)))
      rw [order72_C8_mulThree_gen, map_pow, order72_e9C8Order4Action_gen, hφ])
  exact ⟨(semidirectProductCongr_eq h).trans
    (semidirectProductCongrAut (φ := order72_e9C8Order4Action) order72_C8_mulThree)⟩

theorem order72_e9_c8_semidirect_case_of_gen_eq_order8_pow3
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut ^ 3) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  have h : φ = order72_e9C8Order8Action.comp order72_C8_mulThree.toMonoidHom :=
    order72_e9_c8_action_eq_of_gen (by
      change φ (Multiplicative.ofAdd (1 : ZMod 8)) =
        order72_e9C8Order8Action (order72_C8_mulThree (Multiplicative.ofAdd (1 : ZMod 8)))
      rw [order72_C8_mulThree_gen, map_pow, order72_e9C8Order8Action_gen, hφ])
  exact ⟨(semidirectProductCongr_eq h).trans
    (semidirectProductCongrAut (φ := order72_e9C8Order8Action) order72_C8_mulThree)⟩

theorem order72_e9_c8_semidirect_case_of_gen_eq_order8_pow5
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut ^ 5) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  have h : φ = order72_e9C8Order8Action.comp order72_C8_mulFive.toMonoidHom :=
    order72_e9_c8_action_eq_of_gen (by
      change φ (Multiplicative.ofAdd (1 : ZMod 8)) =
        order72_e9C8Order8Action (order72_C8_mulFive (Multiplicative.ofAdd (1 : ZMod 8)))
      rw [order72_C8_mulFive_gen, map_pow, order72_e9C8Order8Action_gen, hφ])
  exact ⟨(semidirectProductCongr_eq h).trans
    (semidirectProductCongrAut (φ := order72_e9C8Order8Action) order72_C8_mulFive)⟩

theorem order72_e9_c8_semidirect_case_of_gen_eq_order8_pow7
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut ^ 7) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  have h : φ = order72_e9C8Order8Action.comp order72_C8_mulSeven.toMonoidHom :=
    order72_e9_c8_action_eq_of_gen (by
      change φ (Multiplicative.ofAdd (1 : ZMod 8)) =
        order72_e9C8Order8Action (order72_C8_mulSeven (Multiplicative.ofAdd (1 : ZMod 8)))
      rw [order72_C8_mulSeven_gen, map_pow, order72_e9C8Order8Action_gen, hφ])
  exact ⟨(semidirectProductCongr_eq h).trans
    (semidirectProductCongrAut (φ := order72_e9C8Order8Action) order72_C8_mulSeven)⟩

theorem order72_e9_c8_semidirect_cases_of_standard_gen
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : φ (Multiplicative.ofAdd (1 : ZMod 8)) = 1 ∨
      φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_negAut ∨
        φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_reflectAut ∨
          φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order4Aut ∨
            φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
        ElemAbelianRep 3 × Multiplicative (ZMod 8)) ∨
      Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
        order72_E9_C8_neg) ∨
        Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
          order72_E9_C8_reflect) ∨
          Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
            order72_E9_C8_order4) ∨
            Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
              order72_E9_C8_order8) := by
  rcases hφ with h | h | h | h | h
  · exact Or.inl (order72_e9_c8_semidirect_case_of_gen_eq_one φ h)
  · exact Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_eq_neg φ h))
  · exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_eq_reflect φ h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (order72_e9_c8_semidirect_case_of_gen_eq_order4 φ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (order72_e9_c8_semidirect_case_of_gen_eq_order8 φ h))))

theorem order72_e9_c8_semidirect_cases_of_standard_odd_gen
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : φ (Multiplicative.ofAdd (1 : ZMod 8)) = 1 ∨
      φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_negAut ∨
        φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_reflectAut ∨
          φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order4Aut ∨
            φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order4Aut ^ 3 ∨
              φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut ∨
                φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut ^ 3 ∨
                  φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut ^ 5 ∨
                    φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut ^ 7) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
        ElemAbelianRep 3 × Multiplicative (ZMod 8)) ∨
      Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
        order72_E9_C8_neg) ∨
        Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
          order72_E9_C8_reflect) ∨
          Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
            order72_E9_C8_order4) ∨
            Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
              order72_E9_C8_order8) := by
  rcases hφ with h | h | h | h | h | h | h | h | h
  · exact Or.inl (order72_e9_c8_semidirect_case_of_gen_eq_one φ h)
  · exact Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_eq_neg φ h))
  · exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_eq_reflect φ h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (order72_e9_c8_semidirect_case_of_gen_eq_order4 φ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (order72_e9_c8_semidirect_case_of_gen_eq_order4_pow3 φ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (order72_e9_c8_semidirect_case_of_gen_eq_order8 φ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (order72_e9_c8_semidirect_case_of_gen_eq_order8_pow3 φ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (order72_e9_c8_semidirect_case_of_gen_eq_order8_pow5 φ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (order72_e9_c8_semidirect_case_of_gen_eq_order8_pow7 φ h))))

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_one
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      order72_E9_autCode 1) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      ElemAbelianRep 3 × Multiplicative (ZMod 8)) :=
  order72_e9_c8_semidirect_case_of_gen_eq_one φ (order72_E9_autCode_injective hφ)

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_neg
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      order72_E9_autCode order72_E9_negAut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_neg) :=
  order72_e9_c8_semidirect_case_of_gen_eq_neg φ (order72_E9_autCode_injective hφ)

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_reflect
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      order72_E9_autCode order72_E9_reflectAut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) :=
  order72_e9_c8_semidirect_case_of_gen_eq_reflect φ (order72_E9_autCode_injective hφ)

private theorem order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (θ : MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode
        ((MulAut.conj θ) (φ (Multiplicative.ofAdd (1 : ZMod 8)))) =
      order72_E9_autCode order72_E9_reflectAut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  let φ' : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3) :=
    (MulAut.conj θ).toMonoidHom.comp φ
  have hgen : φ' (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_reflectAut :=
    order72_E9_autCode_injective hφ
  obtain ⟨e⟩ := order72_e9_c8_semidirect_case_of_gen_eq_reflect φ' hgen
  exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans e⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_2101
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((2, 1), (0, 1))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect φ
    order72_E9_shearLower.symm
  rw [order72_E9_autCode_injective (hφ.trans order72_E9_reflectLowerShear_code.symm)]
  exact order72_E9_reflectLowerShear_conj_code

theorem order72_e9_c8_branch_case_of_gen_code_eq_2101 {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((2, 1), (0, 1))) :
    Nonempty (G ≃* order72_E9_C8_reflect) := by
  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_code_eq_2101 φ hφ
  exact ⟨e.trans eh⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_2201
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((2, 2), (0, 1))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect φ
    ((order72_E9_shearLower ^ 2).symm)
  rw [order72_E9_autCode_injective (hφ.trans order72_E9_reflectLowerShearSq_code.symm)]
  exact order72_E9_reflectLowerShearSq_conj_code

theorem order72_e9_c8_branch_case_of_gen_code_eq_2201 {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((2, 2), (0, 1))) :
    Nonempty (G ≃* order72_E9_C8_reflect) := by
  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_code_eq_2201 φ hφ
  exact ⟨e.trans eh⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_1002
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((1, 0), (0, 2))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect φ order72_E9_swap
  rw [order72_E9_autCode_injective (hφ.trans order72_E9_reflectSecond_code.symm)]
  exact order72_E9_reflectSecond_conj_code

theorem order72_e9_c8_branch_case_of_gen_code_eq_1002 {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((1, 0), (0, 2))) :
    Nonempty (G ≃* order72_E9_C8_reflect) := by
  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_code_eq_1002 φ hφ
  exact ⟨e.trans eh⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_1102
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((1, 1), (0, 2))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect φ
    (order72_E9_shearLower.trans order72_E9_swap)
  rw [order72_E9_autCode_injective (hφ.trans order72_E9_reflectSecondShearInv_code.symm)]
  exact order72_E9_reflectSecondShearInv_conj_code

theorem order72_e9_c8_branch_case_of_gen_code_eq_1102 {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((1, 1), (0, 2))) :
    Nonempty (G ≃* order72_E9_C8_reflect) := by
  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_code_eq_1102 φ hφ
  exact ⟨e.trans eh⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_1202
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((1, 2), (0, 2))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect φ
    (order72_E9_shearLower.symm.trans order72_E9_swap)
  rw [order72_E9_autCode_injective (hφ.trans order72_E9_reflectSecondShear_code.symm)]
  exact order72_E9_reflectSecondShear_conj_code

theorem order72_e9_c8_branch_case_of_gen_code_eq_1202 {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((1, 2), (0, 2))) :
    Nonempty (G ≃* order72_E9_C8_reflect) := by
  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_code_eq_1202 φ hφ
  exact ⟨e.trans eh⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_0110
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((0, 1), (1, 0))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect φ
    order72_E9_swapReflectBasis.symm
  rw [order72_E9_autCode_injective (hφ.trans order72_E9_reflectSwap_code.symm)]
  exact order72_E9_reflectSwap_conj_code

theorem order72_e9_c8_branch_case_of_gen_code_eq_0110 {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((0, 1), (1, 0))) :
    Nonempty (G ≃* order72_E9_C8_reflect) := by
  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_code_eq_0110 φ hφ
  exact ⟨e.trans eh⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_2011
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((2, 0), (1, 1))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect φ
    (order72_E9_shearLower.symm.trans order72_E9_swapReflectBasis.symm)
  rw [order72_E9_autCode_injective
    (hφ.trans order72_E9_reflectSwapLowerShear_code.symm)]
  exact order72_E9_reflectSwapLowerShear_conj_code

theorem order72_e9_c8_branch_case_of_gen_code_eq_2011 {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((2, 0), (1, 1))) :
    Nonempty (G ≃* order72_E9_C8_reflect) := by
  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_code_eq_2011 φ hφ
  exact ⟨e.trans eh⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_1012
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((1, 0), (1, 2))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect φ
    (((order72_E9_shearLower ^ 2).symm).trans order72_E9_swapReflectBasis.symm)
  rw [order72_E9_autCode_injective
    (hφ.trans order72_E9_reflectSwapLowerShearSq_code.symm)]
  exact order72_E9_reflectSwapLowerShearSq_conj_code

theorem order72_e9_c8_branch_case_of_gen_code_eq_1012 {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((1, 0), (1, 2))) :
    Nonempty (G ≃* order72_E9_C8_reflect) := by
  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_code_eq_1012 φ hφ
  exact ⟨e.trans eh⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_0220
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((0, 2), (2, 0))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect φ
    order72_E9_negSwapReflectBasis.symm
  rw [order72_E9_autCode_injective (hφ.trans order72_E9_reflectNegSwap_code.symm)]
  exact order72_E9_reflectNegSwap_conj_code

theorem order72_e9_c8_branch_case_of_gen_code_eq_0220 {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((0, 2), (2, 0))) :
    Nonempty (G ≃* order72_E9_C8_reflect) := by
  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_code_eq_0220 φ hφ
  exact ⟨e.trans eh⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_2021
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((2, 0), (2, 1))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect φ
    order72_E9_shearPlus.symm
  rw [order72_E9_autCode_injective (hφ.trans order72_E9_reflectUpperShear_code.symm)]
  exact order72_E9_reflectUpperShear_conj_code

theorem order72_e9_c8_branch_case_of_gen_code_eq_2021 {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((2, 0), (2, 1))) :
    Nonempty (G ≃* order72_E9_C8_reflect) := by
  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_code_eq_2021 φ hφ
  exact ⟨e.trans eh⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_1022
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((1, 0), (2, 2))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_reflect) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_reflect φ
    (order72_E9_shearPlus.trans order72_E9_swap)
  rw [order72_E9_autCode_injective
    (hφ.trans order72_E9_reflectSecondUpperShearInv_code.symm)]
  exact order72_E9_reflectSecondUpperShearInv_conj_code

theorem order72_e9_c8_branch_case_of_gen_code_eq_1022 {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      ((1, 0), (2, 2))) :
    Nonempty (G ≃* order72_E9_C8_reflect) := by
  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_code_eq_1022 φ hφ
  exact ⟨e.trans eh⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_order4
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      order72_E9_autCode order72_E9_order4Aut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order4) :=
  order72_e9_c8_semidirect_case_of_gen_eq_order4 φ (order72_E9_autCode_injective hφ)

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_order4_pow3
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      order72_E9_autCode (order72_E9_order4Aut ^ 3)) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order4) :=
  order72_e9_c8_semidirect_case_of_gen_eq_order4_pow3 φ
    (order72_E9_autCode_injective hφ)

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_order8
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      order72_E9_autCode order72_E9_order8Aut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) :=
  order72_e9_c8_semidirect_case_of_gen_eq_order8 φ (order72_E9_autCode_injective hφ)

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_order8_pow3
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      order72_E9_autCode (order72_E9_order8Aut ^ 3)) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) :=
  order72_e9_c8_semidirect_case_of_gen_eq_order8_pow3 φ
    (order72_E9_autCode_injective hφ)

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_order8_pow5
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      order72_E9_autCode (order72_E9_order8Aut ^ 5)) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) :=
  order72_e9_c8_semidirect_case_of_gen_eq_order8_pow5 φ
    (order72_E9_autCode_injective hφ)

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_order8_pow7
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) =
      order72_E9_autCode (order72_E9_order8Aut ^ 7)) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) :=
  order72_e9_c8_semidirect_case_of_gen_eq_order8_pow7 φ
    (order72_E9_autCode_injective hφ)

/-! ### The remaining `GL(2,3)` codes: order-`4` and order-`8` generator images.

The twelve remaining elements of `GL(2,3)` whose order divides `8` are the four order-`4`
elements `[[1,1],[1,2]]`, `[[2,2],[2,1]]`, `[[1,2],[2,2]]`, `[[2,1],[1,1]]` (all conjugate to
`order72_E9_order4Aut`) and the eight order-`8` elements with trace `±1` (conjugate to
`order72_E9_order8Aut` resp. `order72_E9_order8Aut ^ 5`).  For each code we give an explicit
conjugator built from the elementary automorphisms (`shearPlus`, `scaleSecond2`), verified by
`decide`, and conclude that the corresponding semidirect product is the standard
`order4`/`order8` representative. -/

private theorem order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order4
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (θ : MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode
        ((MulAut.conj θ) (φ (Multiplicative.ofAdd (1 : ZMod 8)))) =
      order72_E9_autCode order72_E9_order4Aut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order4) := by
  let φ' : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3) :=
    (MulAut.conj θ).toMonoidHom.comp φ
  have hgen : φ' (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order4Aut :=
    order72_E9_autCode_injective hφ
  obtain ⟨e⟩ := order72_e9_c8_semidirect_case_of_gen_eq_order4 φ' hgen
  exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans e⟩

private theorem order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order8
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (θ : MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode
        ((MulAut.conj θ) (φ (Multiplicative.ofAdd (1 : ZMod 8)))) =
      order72_E9_autCode order72_E9_order8Aut) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  let φ' : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3) :=
    (MulAut.conj θ).toMonoidHom.comp φ
  have hgen : φ' (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut :=
    order72_E9_autCode_injective hφ
  obtain ⟨e⟩ := order72_e9_c8_semidirect_case_of_gen_eq_order8 φ' hgen
  exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans e⟩

private theorem order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order8_pow5
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (θ : MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode
        ((MulAut.conj θ) (φ (Multiplicative.ofAdd (1 : ZMod 8)))) =
      order72_E9_autCode (order72_E9_order8Aut ^ 5)) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  let φ' : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3) :=
    (MulAut.conj θ).toMonoidHom.comp φ
  have hgen : φ' (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut ^ 5 :=
    order72_E9_autCode_injective hφ
  obtain ⟨e⟩ := order72_e9_c8_semidirect_case_of_gen_eq_order8_pow5 φ' hgen
  exact ⟨(semidirectProductCongrConj (φ := φ) θ).trans e⟩

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_1112
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((1, 1), (1, 2))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order4) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order4 φ order72_E9_shearPlus.symm
  have hθ : order72_E9_autCode
      ((MulAut.conj order72_E9_shearPlus) order72_E9_order4Aut) = ((1, 1), (1, 2)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_2221
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((2, 2), (2, 1))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order4) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order4 φ
    ((order72_E9_shearPlus ^ 2).trans order72_E9_scaleSecond2).symm
  have hθ : order72_E9_autCode
      ((MulAut.conj ((order72_E9_shearPlus ^ 2).trans order72_E9_scaleSecond2))
        order72_E9_order4Aut) = ((2, 2), (2, 1)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_1222
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((1, 2), (2, 2))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order4) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order4 φ
    (order72_E9_shearPlus.trans order72_E9_scaleSecond2).symm
  have hθ : order72_E9_autCode
      ((MulAut.conj (order72_E9_shearPlus.trans order72_E9_scaleSecond2))
        order72_E9_order4Aut) = ((1, 2), (2, 2)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_2111
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((2, 1), (1, 1))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order4) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order4 φ
    (order72_E9_shearPlus ^ 2).symm
  have hθ : order72_E9_autCode
      ((MulAut.conj (order72_E9_shearPlus ^ 2)) order72_E9_order4Aut) = ((2, 1), (1, 1)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_0111
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((0, 1), (1, 1))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order8 φ
    (order72_E9_shearPlus ^ 2).symm
  have hθ : order72_E9_autCode
      ((MulAut.conj (order72_E9_shearPlus ^ 2)) order72_E9_order8Aut) = ((0, 1), (1, 1)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_1220
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((1, 2), (2, 0))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order8 φ
    order72_E9_scaleSecond2.symm
  have hθ : order72_E9_autCode
      ((MulAut.conj order72_E9_scaleSecond2) order72_E9_order8Aut) = ((1, 2), (2, 0)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_2122
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((2, 1), (2, 2))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order8 φ order72_E9_shearPlus.symm
  have hθ : order72_E9_autCode
      ((MulAut.conj order72_E9_shearPlus) order72_E9_order8Aut) = ((2, 1), (2, 2)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_2212
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((2, 2), (1, 2))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order8 φ
    (order72_E9_shearPlus.trans order72_E9_scaleSecond2).symm
  have hθ : order72_E9_autCode
      ((MulAut.conj (order72_E9_shearPlus.trans order72_E9_scaleSecond2))
        order72_E9_order8Aut) = ((2, 2), (1, 2)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_0222
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((0, 2), (2, 2))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order8_pow5 φ
    (order72_E9_shearPlus ^ 2).symm
  have hθ : order72_E9_autCode
      ((MulAut.conj (order72_E9_shearPlus ^ 2)) (order72_E9_order8Aut ^ 5)) =
        ((0, 2), (2, 2)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_2110
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((2, 1), (1, 0))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order8_pow5 φ
    order72_E9_scaleSecond2.symm
  have hθ : order72_E9_autCode
      ((MulAut.conj order72_E9_scaleSecond2) (order72_E9_order8Aut ^ 5)) =
        ((2, 1), (1, 0)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_1121
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((1, 1), (2, 1))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order8_pow5 φ
    (order72_E9_shearPlus.trans order72_E9_scaleSecond2).symm
  have hθ : order72_E9_autCode
      ((MulAut.conj (order72_E9_shearPlus.trans order72_E9_scaleSecond2))
        (order72_E9_order8Aut ^ 5)) = ((1, 1), (2, 1)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

private theorem order72_e9_c8_semidirect_case_of_gen_code_eq_1211
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3))
    (hφ : order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = ((1, 2), (1, 1))) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
      order72_E9_C8_order8) := by
  apply order72_e9_c8_semidirect_case_of_gen_conj_code_eq_order8_pow5 φ
    order72_E9_shearPlus.symm
  have hθ : order72_E9_autCode
      ((MulAut.conj order72_E9_shearPlus) (order72_E9_order8Aut ^ 5)) = ((1, 2), (1, 1)) := by
    decide
  rw [order72_E9_autCode_injective (hφ.trans hθ.symm)]
  decide

/-- The nine elements of `C3 × C3` as monomials in the standard generators. -/
theorem order72_E9_total_cases (k : ElemAbelianRep 3) :
    k = 1 ∨ k = order72_E9_g1 ∨ k = order72_E9_g1 ^ 2 ∨
      k = order72_E9_g2 ∨ k = order72_E9_g1 * order72_E9_g2 ∨
        k = order72_E9_g1 ^ 2 * order72_E9_g2 ∨ k = order72_E9_g2 ^ 2 ∨
          k = order72_E9_g1 * order72_E9_g2 ^ 2 ∨
            k = order72_E9_g1 ^ 2 * order72_E9_g2 ^ 2 := by
  revert k
  decide

/-- The code of a generator image, computed from its two values. -/
private theorem order72_e9_c8_code_of_gen_values
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    {x y : ElemAbelianRep 3} {c : (Nat × Nat) × (Nat × Nat)}
    (h1 : φ (Multiplicative.ofAdd (1 : ZMod 8)) order72_E9_g1 = x)
    (h2 : φ (Multiplicative.ofAdd (1 : ZMod 8)) order72_E9_g2 = y)
    (hc : (order72_E9_coord x, order72_E9_coord y) = c) :
    order72_E9_autCode (φ (Multiplicative.ofAdd (1 : ZMod 8))) = c := by
  change (order72_E9_coord (φ (Multiplicative.ofAdd (1 : ZMod 8)) order72_E9_g1),
      order72_E9_coord (φ (Multiplicative.ofAdd (1 : ZMod 8)) order72_E9_g2)) = c
  rw [h1, h2]
  exact hc

/-- The unique function `C3 × C3 → C3 × C3` sending the standard generators to `x` and
`y` (no hom proof needed; used to evaluate iterates of a pinned automorphism). -/
def order72_E9_homOfValuesFun (x y : ElemAbelianRep 3) :
    ElemAbelianRep 3 → ElemAbelianRep 3 :=
  fun p => x ^ (Multiplicative.toAdd p.1).val * y ^ (Multiplicative.toAdd p.2).val

theorem order72_E9_fst_eq_g1_pow (p1 : Multiplicative (ZMod 3)) :
    ((p1, 1) : ElemAbelianRep 3) = order72_E9_g1 ^ (Multiplicative.toAdd p1).val := by
  let j : ZMod 3 := Multiplicative.toAdd p1
  have hx0 : Multiplicative.ofAdd j = p1 := ofAdd_toAdd p1
  rw [← hx0]
  ext
  · simp only [order72_E9_g1, Prod.pow_fst]
    rw [← ofAdd_nsmul]
    simp
  · simp [order72_E9_g1]

theorem order72_E9_snd_eq_g2_pow (p2 : Multiplicative (ZMod 3)) :
    ((1, p2) : ElemAbelianRep 3) = order72_E9_g2 ^ (Multiplicative.toAdd p2).val := by
  let j : ZMod 3 := Multiplicative.toAdd p2
  have hx0 : Multiplicative.ofAdd j = p2 := ofAdd_toAdd p2
  rw [← hx0]
  ext
  · simp [order72_E9_g2]
  · simp only [order72_E9_g2, Prod.pow_snd]
    rw [← ofAdd_nsmul]
    simp

/-- An automorphism pinned to values `x, y` on the generators agrees everywhere with the
explicit function `order72_E9_homOfValuesFun x y`. -/
theorem order72_E9_apply_eq_homOfValuesFun
    (f : MulAut (ElemAbelianRep 3)) {x y : ElemAbelianRep 3}
    (h1 : f order72_E9_g1 = x) (h2 : f order72_E9_g2 = y) (p : ElemAbelianRep 3) :
    f p = order72_E9_homOfValuesFun x y p := by
  obtain ⟨p1, p2⟩ := p
  have hdecomp : ((p1, p2) : ElemAbelianRep 3) = (p1, 1) * (1, p2) := by ext <;> simp
  conv_lhs => rw [hdecomp, map_mul, order72_E9_fst_eq_g1_pow, order72_E9_snd_eq_g2_pow,
    map_pow, map_pow, h1, h2]
  rfl

/-- Iterates of a pinned automorphism are iterates of the explicit function. -/
theorem order72_E9_pow_eq_homOfValuesFun_iter
    (f : MulAut (ElemAbelianRep 3)) {x y : ElemAbelianRep 3}
    (h1 : f order72_E9_g1 = x) (h2 : f order72_E9_g2 = y) (n : ℕ) (p : ElemAbelianRep 3) :
    (f ^ n) p = (order72_E9_homOfValuesFun x y)^[n] p := by
  induction n generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, order72_E9_apply_eq_homOfValuesFun f h1 h2,
      ih, Function.iterate_succ_apply]

/-- **The `E9 ⋊ C8` branch is fully classified**: every action
`C8 → Aut(C3 × C3) = GL(2,3)` gives one of the five standard semidirect products
(direct product, central inversion, reflection, order-`4` or order-`8` faithful action).
The proof enumerates the `9 × 9` pairs of generator images: the `32` pairs that arise from
automorphisms of order dividing `8` are each reduced to a standard representative (via the
code-case theorems above), and each of the remaining `49` pairs contradicts
`φ(gen) ^ 8 = 1`. -/
theorem order72_e9_c8_semidirect_cases
    (φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)) :
    Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
        ElemAbelianRep 3 × Multiplicative (ZMod 8)) ∨
      Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
        order72_E9_C8_neg) ∨
      Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
        order72_E9_C8_reflect) ∨
      Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
        order72_E9_C8_order4) ∨
      Nonempty (SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ ≃*
        order72_E9_C8_order8) := by
  have hf8 := order72_e9_c8_action_gen_pow8 φ
  rcases order72_E9_total_cases (φ (Multiplicative.ofAdd (1 : ZMod 8)) order72_E9_g1)
    with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
    rcases order72_E9_total_cases (φ (Multiplicative.ofAdd (1 : ZMod 8)) order72_E9_g2)
    with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 <;>
    first
    | exact Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_one φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))
    | exact Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_neg φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_reflect φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_2101 φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_2201 φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_1002 φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_1102 φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_1202 φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_0110 φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_2011 φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_1012 φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_0220 φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_2021 φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inl (order72_e9_c8_semidirect_case_of_gen_code_eq_1022 φ
        (order72_e9_c8_code_of_gen_values h1 h2 (by decide)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl
        (order72_e9_c8_semidirect_case_of_gen_code_eq_order4 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl
        (order72_e9_c8_semidirect_case_of_gen_code_eq_order4_pow3 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl
        (order72_e9_c8_semidirect_case_of_gen_code_eq_1112 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl
        (order72_e9_c8_semidirect_case_of_gen_code_eq_2221 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl
        (order72_e9_c8_semidirect_case_of_gen_code_eq_1222 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inl
        (order72_e9_c8_semidirect_case_of_gen_code_eq_2111 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_order8 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_order8_pow3 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_order8_pow5 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_order8_pow7 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_0111 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_1220 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_2122 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_2212 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_0222 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_2110 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_1121 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr
        (order72_e9_c8_semidirect_case_of_gen_code_eq_1211 φ
          (order72_e9_c8_code_of_gen_values h1 h2 (by decide))))))
    | exfalso
      have hg1 : (φ (Multiplicative.ofAdd (1 : ZMod 8)) ^ 8) order72_E9_g1 =
        order72_E9_g1 := by rw [hf8]; rfl
      have hg2 : (φ (Multiplicative.ofAdd (1 : ZMod 8)) ^ 8) order72_E9_g2 =
        order72_E9_g2 := by rw [hf8]; rfl
      rw [order72_E9_pow_eq_homOfValuesFun_iter _ h1 h2 8 order72_E9_g1] at hg1
      rw [order72_E9_pow_eq_homOfValuesFun_iter _ h1 h2 8 order72_E9_g2] at hg2
      first
      | exact absurd hg1 (by decide)
      | exact absurd hg2 (by decide)

/-- The `G`-level version of the `E9 ⋊ C8` classification. -/
theorem order72_e9_c8_branch_cases {G : Type*} [Group G]
    {φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3)}
    (e : G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ) :
    Nonempty (G ≃* ElemAbelianRep 3 × Multiplicative (ZMod 8)) ∨
      Nonempty (G ≃* order72_E9_C8_neg) ∨
      Nonempty (G ≃* order72_E9_C8_reflect) ∨
      Nonempty (G ≃* order72_E9_C8_order4) ∨
      Nonempty (G ≃* order72_E9_C8_order8) := by
  rcases order72_e9_c8_semidirect_cases φ with h | h | h | h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inl ⟨e.trans eh⟩)
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩)))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans eh⟩)))

/-- The seven nontrivial elements of `C3 × C3`, listed in the standard basis. -/
theorem order72_E9_nontrivial_cases (k : ElemAbelianRep 3) (hk : k ≠ 1) :
    k = order72_E9_g1 ∨
    k = order72_E9_g1 ^ 2 ∨
    k = order72_E9_g2 ∨
    k = order72_E9_g2 ^ 2 ∨
    k = order72_E9_g1 * order72_E9_g2 ∨
    k = order72_E9_g1 ^ 2 * order72_E9_g2 ∨
    k = order72_E9_g1 * order72_E9_g2 ^ 2 ∨
    k = order72_E9_g1 ^ 2 * order72_E9_g2 ^ 2 := by
  revert k
  decide

/-- Any nontrivial element of `C3 × C3` can be made the first basis vector by a source
automorphism. -/
theorem order72_E9_exists_aut_map_g1 (k : ElemAbelianRep 3) (hk : k ≠ 1) :
    ∃ σ : ElemAbelianRep 3 ≃* ElemAbelianRep 3, σ order72_E9_g1 = k := by
  rcases order72_E9_nontrivial_cases k hk with h | h | h | h | h | h | h | h
  · subst k
    exact ⟨MulEquiv.refl _, rfl⟩
  · subst k
    exact ⟨order72_E9_scaleFirst2, order72_E9_scaleFirst2_g1⟩
  · subst k
    exact ⟨order72_E9_swap, order72_E9_swap_g1⟩
  · subst k
    refine ⟨order72_E9_swap.trans order72_E9_scaleSecond2, ?_⟩
    change order72_E9_scaleSecond2 (order72_E9_swap order72_E9_g1) = order72_E9_g2 ^ 2
    rw [order72_E9_swap_g1, order72_E9_scaleSecond2_g2]
  · subst k
    refine ⟨order72_E9_swap.trans order72_E9_shearPlus, ?_⟩
    change order72_E9_shearPlus (order72_E9_swap order72_E9_g1) =
      order72_E9_g1 * order72_E9_g2
    rw [order72_E9_swap_g1, order72_E9_shearPlus_g2]
  · subst k
    refine ⟨(order72_E9_swap.trans order72_E9_shearPlus).trans order72_E9_scaleFirst2, ?_⟩
    change order72_E9_scaleFirst2
      (order72_E9_shearPlus (order72_E9_swap order72_E9_g1)) =
        order72_E9_g1 ^ 2 * order72_E9_g2
    rw [order72_E9_swap_g1, order72_E9_shearPlus_g2]
    decide
  · subst k
    refine ⟨(order72_E9_swap.trans order72_E9_shearPlus).trans order72_E9_scaleSecond2, ?_⟩
    change order72_E9_scaleSecond2
      (order72_E9_shearPlus (order72_E9_swap order72_E9_g1)) =
        order72_E9_g1 * order72_E9_g2 ^ 2
    rw [order72_E9_swap_g1, order72_E9_shearPlus_g2]
    decide
  · subst k
    refine ⟨(order72_E9_swap.trans order72_E9_shearPlus).trans
      (order72_E9_scaleFirst2.trans order72_E9_scaleSecond2), ?_⟩
    change order72_E9_scaleSecond2
      (order72_E9_scaleFirst2
        (order72_E9_shearPlus (order72_E9_swap order72_E9_g1))) =
        order72_E9_g1 ^ 2 * order72_E9_g2 ^ 2
    rw [order72_E9_swap_g1, order72_E9_shearPlus_g2]
    decide

/-! ### `AbelianP2P 2 ≃ ℤ/4 × ℤ/2` has no order-`3` automorphism.

Proof sketch (no brute-force search over `Equiv.Perm H`): write `e1 = (1,0)`, `e2 = (0,1)`,
`z = e1² = (2,0)`. Every order-`4` element of `H` squares to the same `z`, so `z` is fixed
by any automorphism (`f z = f (e1 ^ 2) = (f e1) ^ 2 = z`, since `f e1` is again an order-`4`
element). Given `f ^ 3 = 1`: tracking the single generator `e2` through `f` directly (no
permutation enumeration) shows `f e2 = e2` (the alternative `f e2 = e2 * z` immediately
contradicts `f ^ 3 = 1` via a 2-line computation). A parallel argument on `e1` (using
`f e2 = e2` already established) then forces `f e1 = e1`, and since `e1, e2` generate `H`,
`f = 1`. -/

abbrev H2 := Multiplicative (ZMod 4) × Multiplicative (ZMod 2)

def h2e1 : H2 := (Multiplicative.ofAdd (1 : ZMod 4), 1)
def h2e2 : H2 := (1, Multiplicative.ofAdd (1 : ZMod 2))
def h2z : H2 := (Multiplicative.ofAdd (2 : ZMod 4), 1)

theorem h2e1sq : h2e1 ^ 2 = h2z := by decide
theorem h2e1pow4 : h2e1 ^ 4 = 1 := by decide
theorem h2e1sq_ne1 : h2e1 ^ 2 ≠ 1 := by decide
theorem h2zsq : h2z ^ 2 = 1 := by decide
theorem h2e2sq : h2e2 ^ 2 = 1 := by decide
theorem h2zne1 : h2z ≠ 1 := by decide
theorem h2e2nez : h2e2 ≠ h2z := by decide
theorem h2e2ne1 : h2e2 ≠ 1 := by decide

theorem h2sq_eq_z : ∀ x : H2, x ^ 4 = 1 → x ^ 2 ≠ 1 → x ^ 2 = h2z := by decide

theorem h2order2_mem : ∀ x : H2, x ^ 2 = 1 →
    (x = 1 ∨ x = h2z ∨ x = h2e2 ∨ x = h2e2 * h2z) := by decide

theorem h2order4_mem : ∀ x : H2, x ^ 4 = 1 → x ^ 2 ≠ 1 →
    (x = h2e1 ∨ x = h2e1⁻¹ ∨ x = h2e1 * h2e2 ∨ x = h2e1⁻¹ * h2e2) := by decide

theorem h2gen : ∀ x : H2, x = 1 ∨ x = h2e1 ∨ x = h2e1 ^ 2 ∨ x = h2e1 ^ 3 ∨ x = h2e2 ∨
    x = h2e1 * h2e2 ∨ x = h2e1 ^ 2 * h2e2 ∨ x = h2e1 ^ 3 * h2e2 := by decide

theorem h2_hom_ext {M : Type*} [Group M] {φ ψ : H2 →* M}
    (h1 : φ h2e1 = ψ h2e1) (h2 : φ h2e2 = ψ h2e2) : φ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases h2gen x with h | h | h | h | h | h | h | h <;>
    simp [h, map_pow, map_mul, h1, h2]

private noncomputable def order72_c4InvChar : CyclicRep 4 →* (ZMod 9)ˣ :=
  zmodActionHom 4 (-1 : (ZMod 9)ˣ) (by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    simp [sq])

private noncomputable def order72_c2InvChar : CyclicRep 2 →* (ZMod 9)ˣ :=
  zmodActionHom 2 (-1 : (ZMod 9)ˣ) (by simp [sq])

@[simp] private theorem order72_c4InvChar_gen :
    order72_c4InvChar (Multiplicative.ofAdd (1 : ZMod 4)) = (-1 : (ZMod 9)ˣ) := by
  rw [order72_c4InvChar, zmodActionHom_gen]

@[simp] private theorem order72_c2InvChar_gen :
    order72_c2InvChar (Multiplicative.ofAdd (1 : ZMod 2)) = (-1 : (ZMod 9)ˣ) := by
  rw [order72_c2InvChar, zmodActionHom_gen]

noncomputable def order72_c9H2FstInvAction : H2 →* MulAut (CyclicRep 9) :=
  (unitAutHom (p := 9)).comp (order72_c4InvChar.comp (MonoidHom.fst _ _))

noncomputable def order72_c9H2SndInvAction : H2 →* MulAut (CyclicRep 9) :=
  (unitAutHom (p := 9)).comp (order72_c2InvChar.comp (MonoidHom.snd _ _))

noncomputable def order72_c9H2ProdInvAction : H2 →* MulAut (CyclicRep 9) :=
  (unitAutHom (p := 9)).comp
    ((order72_c4InvChar.comp (MonoidHom.fst _ _)) *
      (order72_c2InvChar.comp (MonoidHom.snd _ _)))

@[simp] theorem order72_c9H2FstInvAction_e1 :
    order72_c9H2FstInvAction h2e1 = order72_c9InvAut := by
  simp [order72_c9H2FstInvAction, h2e1, order72_c9InvAut]

@[simp] theorem order72_c9H2FstInvAction_e2 :
    order72_c9H2FstInvAction h2e2 = 1 := by
  ext x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  simp [order72_c9H2FstInvAction, h2e2]

@[simp] theorem order72_c9H2SndInvAction_e1 :
    order72_c9H2SndInvAction h2e1 = 1 := by
  ext x
  obtain ⟨m, rfl⟩ := Multiplicative.ofAdd.surjective x
  simp [order72_c9H2SndInvAction, h2e1]

@[simp] theorem order72_c9H2SndInvAction_e2 :
    order72_c9H2SndInvAction h2e2 = order72_c9InvAut := by
  simp [order72_c9H2SndInvAction, h2e2, order72_c9InvAut]

@[simp] theorem order72_c9H2ProdInvAction_e1 :
    order72_c9H2ProdInvAction h2e1 = order72_c9InvAut := by
  simp [order72_c9H2ProdInvAction, h2e1, order72_c9InvAut]

@[simp] theorem order72_c9H2ProdInvAction_e2 :
    order72_c9H2ProdInvAction h2e2 = order72_c9InvAut := by
  simp [order72_c9H2ProdInvAction, h2e2, order72_c9InvAut]

abbrev order72_C9_H2_fstInv : Type :=
  SemidirectProduct (CyclicRep 9) H2 order72_c9H2FstInvAction

abbrev order72_C9_H2_sndInv : Type :=
  SemidirectProduct (CyclicRep 9) H2 order72_c9H2SndInvAction

abbrev order72_C9_H2_prodInv : Type :=
  SemidirectProduct (CyclicRep 9) H2 order72_c9H2ProdInvAction

theorem order72_c9_h2_action_cases (φ : H2 →* MulAut (CyclicRep 9)) :
    φ = 1 ∨ φ = order72_c9H2FstInvAction ∨
      φ = order72_c9H2SndInvAction ∨ φ = order72_c9H2ProdInvAction := by
  have hcard : Nat.card H2 = 8 := by
    rw [H2, Nat.card_prod, card_cyclicRep (by norm_num : (4 : ℕ) ≠ 0),
      card_cyclicRep (by norm_num : (2 : ℕ) ≠ 0)]
  rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ h2e1 with h1 | h1
  · rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ h2e2 with h2 | h2
    · left
      apply h2_hom_ext <;> simp [h1, h2]
    · right; right; left
      apply h2_hom_ext <;> simp [h1, h2]
  · rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ h2e2 with h2 | h2
    · right; left
      apply h2_hom_ext <;> simp [h1, h2]
    · right; right; right
      apply h2_hom_ext <;> simp [h1, h2]

theorem order72_c9_h2_semidirect_cases (φ : H2 →* MulAut (CyclicRep 9)) :
    Nonempty (SemidirectProduct (CyclicRep 9) H2 φ ≃* CyclicRep 9 × H2) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) H2 φ ≃* order72_C9_H2_fstInv) ∨
        Nonempty (SemidirectProduct (CyclicRep 9) H2 φ ≃* order72_C9_H2_sndInv) ∨
          Nonempty (SemidirectProduct (CyclicRep 9) H2 φ ≃* order72_C9_H2_prodInv) := by
  rcases order72_c9_h2_action_cases φ with hφ | hφ | hφ | hφ
  · exact Or.inl ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · exact Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨semidirectProductCongr_eq hφ⟩))

theorem order72_c9_h2_branch_cases {G : Type*} [Group G] {φ : H2 →* MulAut (CyclicRep 9)}
    (e : G ≃* SemidirectProduct (CyclicRep 9) H2 φ) :
    Nonempty (G ≃* CyclicRep 9 × H2) ∨
      Nonempty (G ≃* order72_C9_H2_fstInv) ∨
        Nonempty (G ≃* order72_C9_H2_sndInv) ∨
          Nonempty (G ≃* order72_C9_H2_prodInv) := by
  rcases order72_c9_h2_semidirect_cases φ with h | h | h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inl ⟨e.trans eh⟩)
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨e.trans eh⟩))

theorem card_mulAut_abelianP2P_two_no_order_three :
    ∀ f : MulAut H2, f ^ 3 = 1 → f = 1 := by
  intro f hf3
  have hfapp : ∀ g : H2, (f ^ 3) g = g := by intro g; rw [hf3]; rfl
  have hfe1_4 : (f h2e1) ^ 4 = 1 := by rw [← map_pow, h2e1pow4, map_one]
  have hfe1_sq_ne1 : (f h2e1) ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro hcontra
    exact h2e1sq_ne1 (f.injective (by rw [hcontra, map_one]))
  have hfe1_sq : (f h2e1) ^ 2 = h2z := h2sq_eq_z (f h2e1) hfe1_4 hfe1_sq_ne1
  have hfz : f h2z = h2z := by rw [← h2e1sq, map_pow, hfe1_sq, h2e1sq]
  have hfe2_sq : (f h2e2) ^ 2 = 1 := by rw [← map_pow, h2e2sq, map_one]
  have hfe2_ne1 : f h2e2 ≠ 1 := fun h => h2e2ne1 (f.injective (by rw [h, map_one]))
  have hfe2_nez : f h2e2 ≠ h2z := fun h => h2e2nez (f.injective (h.trans hfz.symm))
  have hfe2_cases : f h2e2 = h2e2 ∨ f h2e2 = h2e2 * h2z := by
    rcases h2order2_mem (f h2e2) hfe2_sq with h | h | h | h
    · exact absurd h hfe2_ne1
    · exact absurd h hfe2_nez
    · exact Or.inl h
    · exact Or.inr h
  have hfe2 : f h2e2 = h2e2 := by
    rcases hfe2_cases with h | h
    · exact h
    · exfalso
      have hf2e2 : f (f h2e2) = h2e2 := by
        rw [h, map_mul, h, hfz, mul_assoc, ← sq, h2zsq, mul_one]
      have h3 : f (f (f h2e2)) = f h2e2 := congrArg f hf2e2
      have h3' : f (f (f h2e2)) = h2e2 := hfapp h2e2
      have hthis : f h2e2 = h2e2 := h3.symm.trans h3'
      rw [h] at hthis
      have heq2 : h2e2 * h2z = h2e2 * 1 := by rw [mul_one]; exact hthis
      exact h2zne1 (mul_left_cancel heq2)
  have hfe1 : f h2e1 = h2e1 := by
    rcases h2order4_mem (f h2e1) hfe1_4 hfe1_sq_ne1 with h | h | h | h
    · exact h
    all_goals {
      exfalso
      have hf3e1 : (f ^ 3) h2e1 = h2e1 := hfapp h2e1
      have heq : f (f (f h2e1)) = h2e1 := hf3e1
      rw [h] at heq
      simp only [map_mul, map_inv, hfe2] at heq
      rw [h] at heq
      simp only [map_mul, map_inv, hfe2] at heq
      rw [h] at heq
      revert heq
      decide
    }
  apply DFunLike.ext
  intro x
  change f x = x
  rcases h2gen x with h | h | h | h | h | h | h | h <;>
    simp [h, map_pow, map_mul, hfe1, hfe2]

/-! ### `DihedralGroup 4` has no order-`3` automorphism.

Same technique as `AbelianP2P 2`, adapted to the (non-abelian) dihedral relations. There
are only **two** order-`4` elements here (`r 1`, `r 3` — reflections all have order `2`),
so `f (r 1)` is pinned directly by the coprimality of `3` and `|Sym(2\text{-set})| = 2` (no
separate "square-to-`z`" detour needed for this half). The order-`2` generator `sr 0` then
has **four** candidate images (the four reflections), ruled down to the fixed choice by
tracking the orbit of `sr 0` through `f` via `f³ = 1`, using left-multiplication bookkeeping
(`d1 ^ k * d2`, not `d2 * d1 ^ k` — the group is non-abelian, unlike the `H2` case above). -/

private def d4d1 : DihedralGroup 4 := DihedralGroup.r 1
private def d4d2 : DihedralGroup 4 := DihedralGroup.sr 0
private def d4z : DihedralGroup 4 := DihedralGroup.r 2

private theorem d4d1sq : d4d1 ^ 2 = d4z := by decide
private theorem d4d1pow3 : d4d1 ^ 3 ≠ 1 := by decide
private theorem d4d1pow4 : d4d1 ^ 4 = 1 := by decide
private theorem d4d1sq_ne1 : d4d1 ^ 2 ≠ 1 := by decide
private theorem d4d1ne1 : d4d1 ≠ 1 := by decide
private theorem d4d1ned1inv : d4d1 ≠ d4d1⁻¹ := by decide
private theorem d4d2sq : d4d2 ^ 2 = 1 := by decide
private theorem d4zne1 : d4z ≠ 1 := by decide
private theorem d4d2nez : d4d2 ≠ d4z := by decide
private theorem d4d2ne1 : d4d2 ≠ 1 := by decide

private theorem d4order4_mem : ∀ x : DihedralGroup 4, x ^ 4 = 1 → x ^ 2 ≠ 1 →
    (x = d4d1 ∨ x = d4d1⁻¹) := by decide

private theorem d4order2_mem : ∀ x : DihedralGroup 4, x ^ 2 = 1 →
    (x = 1 ∨ x = d4z ∨ x = d4d2 ∨ x = d4d1 * d4d2 ∨ x = d4d1 ^ 2 * d4d2 ∨
      x = d4d1 ^ 3 * d4d2) := by decide

private theorem d4gen : ∀ x : DihedralGroup 4, x = 1 ∨ x = d4d1 ∨ x = d4d1 ^ 2 ∨
    x = d4d1 ^ 3 ∨ x = d4d2 ∨ x = d4d1 * d4d2 ∨ x = d4d1 ^ 2 * d4d2 ∨
    x = d4d1 ^ 3 * d4d2 := by decide

private theorem d4calc1 : d4d1 * (d4d1 * d4d2) = d4d1 ^ 2 * d4d2 := by decide
private theorem d4calc2 : d4d1 ^ 2 * (d4d1 * d4d2) = d4d1 ^ 3 * d4d2 := by decide
private theorem d4calc3 : d4d1 ^ 2 * (d4d1 ^ 2 * d4d2) = d4d2 := by decide
private theorem d4calc4 : d4d1 ^ 3 * (d4d1 ^ 3 * d4d2) = d4d1 ^ 2 * d4d2 := by decide
private theorem d4calc5 : d4d1 ^ 2 * (d4d1 ^ 3 * d4d2) = d4d1 * d4d2 := by decide

theorem card_mulAut_dihedralGroup_four_no_order_three :
    ∀ f : MulAut (DihedralGroup 4), f ^ 3 = 1 → f = 1 := by
  intro f hf3
  have hfapp : ∀ g : DihedralGroup 4, (f ^ 3) g = g := by intro g; rw [hf3]; rfl
  have hfe1_4 : (f d4d1) ^ 4 = 1 := by rw [← map_pow, d4d1pow4, map_one]
  have hfe1_sq_ne1 : (f d4d1) ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro hcontra
    exact d4d1sq_ne1 (f.injective (by rw [hcontra, map_one]))
  have hfe1 : f d4d1 = d4d1 := by
    rcases d4order4_mem (f d4d1) hfe1_4 hfe1_sq_ne1 with h | h
    · exact h
    · exfalso
      have hf2 : f (f d4d1) = d4d1 := by rw [h, map_inv, h, inv_inv]
      have h3 : f (f (f d4d1)) = f d4d1 := congrArg f hf2
      have h3' : f (f (f d4d1)) = d4d1 := hfapp d4d1
      have heq : f d4d1 = d4d1 := h3.symm.trans h3'
      rw [h] at heq
      exact d4d1ned1inv heq.symm
  have hfz : f d4z = d4z := by rw [← d4d1sq, map_pow, hfe1]
  have hfe2_sq : (f d4d2) ^ 2 = 1 := by rw [← map_pow, d4d2sq, map_one]
  have hfe2_ne1 : f d4d2 ≠ 1 := fun h => d4d2ne1 (f.injective (by rw [h, map_one]))
  have hfe2_nez : f d4d2 ≠ d4z := fun h => d4d2nez (f.injective (h.trans hfz.symm))
  have hfe2_cases : f d4d2 = d4d2 ∨ f d4d2 = d4d1 * d4d2 ∨ f d4d2 = d4d1 ^ 2 * d4d2 ∨
      f d4d2 = d4d1 ^ 3 * d4d2 := by
    rcases d4order2_mem (f d4d2) hfe2_sq with h | h | h | h | h | h
    · exact absurd h hfe2_ne1
    · exact absurd h hfe2_nez
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hfe2 : f d4d2 = d4d2 := by
    rcases hfe2_cases with h | h | h | h
    · exact h
    · exfalso
      have hf2 : f (f d4d2) = d4d1 ^ 2 * d4d2 := by rw [h, map_mul, h, hfe1, d4calc1]
      have hf3' : f (f (f d4d2)) = d4d1 ^ 3 * d4d2 := by
        rw [hf2, map_mul, map_pow, hfe1, h, d4calc2]
      have h3' : f (f (f d4d2)) = d4d2 := hfapp d4d2
      rw [hf3'] at h3'
      exact d4d1pow3 (mul_right_cancel (a := d4d1 ^ 3) (b := d4d2) (by rw [one_mul]; exact h3'))
    · exfalso
      have hf2 : f (f d4d2) = d4d2 := by rw [h, map_mul, map_pow, hfe1, h, d4calc3]
      have hf3' : f (f (f d4d2)) = d4d1 ^ 2 * d4d2 := (congrArg f hf2).trans h
      have h3' : f (f (f d4d2)) = d4d2 := hfapp d4d2
      rw [hf3'] at h3'
      exact d4d1sq_ne1 (mul_right_cancel (a := d4d1 ^ 2) (b := d4d2) (by rw [one_mul]; exact h3'))
    · exfalso
      have hf2 : f (f d4d2) = d4d1 ^ 2 * d4d2 := by rw [h, map_mul, map_pow, hfe1, h, d4calc4]
      have hf3' : f (f (f d4d2)) = d4d1 * d4d2 := by
        rw [hf2, map_mul, map_pow, hfe1, h, d4calc5]
      have h3' : f (f (f d4d2)) = d4d2 := hfapp d4d2
      rw [hf3'] at h3'
      exact d4d1ne1 (mul_right_cancel (a := d4d1) (b := d4d2) (by rw [one_mul]; exact h3'))
  apply DFunLike.ext
  intro x
  change f x = x
  rcases d4gen x with h | h | h | h | h | h | h | h <;>
    simp [h, map_pow, map_mul, hfe1, hfe2]

/-! ### `QuaternionGroup 2` and `ElementaryP3 2` genuinely admit order-`3` automorphisms.

Unlike the three types above, `Aut(Q8) ≅ S₄` (order `24`) and `Aut((ZMod 2)³) ≅ GL(3,2)`
(order `168`) both contain order-`3` elements, so the Sylow-2-normal branch has genuinely
new (not-direct-product) semidirect products for these two `H`-types. This section builds
one concrete order-`3` automorphism for each — the classical constructions (cyclically
permuting `i, j, k` for `Q8`; the companion matrix of the irreducible `x² + x + 1` over
`𝔽₂`, fixing one coordinate and rotating the other two, for `(ZMod 2)³`) — each verified by
a *small* `decide` (an `8 × 8` multiplicativity check, nothing like the rejected
`Equiv.Perm`-search scale).  The later sections prove that every nontrivial order-`3`
automorphism is conjugate to the corresponding representative and package that fact for
homomorphisms `φ : P →* MulAut H` with `Nat.card P = 9`. -/

open QuaternionGroup in
/-- The cyclic order-`3` automorphism of `Q8` permuting `i ↦ j ↦ k ↦ i` (and correspondingly
`-i ↦ -j ↦ -k ↦ -i`), where `i = a 1`, `j = xa 0`, `k = i * j = xa 3`. -/
def q8CycFun : QuaternionGroup 2 → QuaternionGroup 2
  | .a 0 => .a 0
  | .a 1 => .xa 0
  | .a 2 => .a 2
  | .a 3 => .xa 2
  | .xa 0 => .xa 3
  | .xa 1 => .a 3
  | .xa 2 => .xa 1
  | .xa 3 => .a 1

open QuaternionGroup in
private def q8CycInvFun : QuaternionGroup 2 → QuaternionGroup 2
  | .a 0 => .a 0
  | .a 1 => .xa 3
  | .a 2 => .a 2
  | .a 3 => .xa 1
  | .xa 0 => .a 1
  | .xa 1 => .xa 2
  | .xa 2 => .a 3
  | .xa 3 => .xa 0

private theorem q8Cyc_left_inv : ∀ x : QuaternionGroup 2, q8CycInvFun (q8CycFun x) = x := by decide
private theorem q8Cyc_right_inv : ∀ x : QuaternionGroup 2, q8CycFun (q8CycInvFun x) = x := by
  decide
private theorem q8Cyc_mul : ∀ x y : QuaternionGroup 2, q8CycFun (x * y) = q8CycFun x * q8CycFun y :=
  by decide

/-- The concrete order-`3` automorphism of `Q8`. -/
def q8Cyc : MulAut (QuaternionGroup 2) where
  toFun := q8CycFun
  invFun := q8CycInvFun
  left_inv := q8Cyc_left_inv
  right_inv := q8Cyc_right_inv
  map_mul' := q8Cyc_mul

theorem q8Cyc_apply (x : QuaternionGroup 2) : q8Cyc x = q8CycFun x := rfl

open QuaternionGroup in
theorem q8Cyc_pow3 : q8Cyc ^ 3 = 1 := by
  apply DFunLike.ext
  intro x
  change q8Cyc (q8Cyc (q8Cyc x)) = x
  simp only [q8Cyc_apply]
  revert x
  decide

open QuaternionGroup in
theorem q8Cyc_ne_one : q8Cyc ≠ 1 := by
  intro h
  have heq : q8Cyc (a 1) = a 1 := by rw [h]; rfl
  rw [q8Cyc_apply] at heq
  simp [q8CycFun] at heq

/-- Standard nontrivial action of `C9` on `Q8`, factoring through its quotient of order `3`. -/
noncomputable def q8CycActionC9 : CyclicRep 9 →* MulAut (QuaternionGroup 2) :=
  zmodActionHom 9 q8Cyc (by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, q8Cyc_pow3, one_pow])

/-- Standard nontrivial action of `C3 × C3` on `Q8`, nontrivial on the first factor. -/
noncomputable def q8CycActionE9 : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2) :=
  (zmodActionHom 3 q8Cyc q8Cyc_pow3).comp (MonoidHom.fst (CyclicRep 3) (CyclicRep 3))

open QuaternionGroup in
@[simp] theorem q8CycActionC9_gen :
    q8CycActionC9 (Multiplicative.ofAdd (1 : ZMod 9)) = q8Cyc := by
  rw [q8CycActionC9, zmodActionHom_gen]

open QuaternionGroup in
@[simp] theorem q8CycActionE9_fst_gen :
    q8CycActionE9 (Multiplicative.ofAdd (1 : ZMod 3), 1) = q8Cyc := by
  rw [q8CycActionE9]
  simp [zmodActionHom_gen]

open QuaternionGroup in
@[simp] theorem q8CycActionE9_snd_gen :
    q8CycActionE9 (1, Multiplicative.ofAdd (1 : ZMod 3)) = 1 := by
  rw [q8CycActionE9]
  simp

theorem q8CycActionC9_ne_one : q8CycActionC9 ≠ 1 := by
  intro h
  have hval : q8CycActionC9 (Multiplicative.ofAdd (1 : ZMod 9)) = 1 := by rw [h]; rfl
  rw [q8CycActionC9_gen] at hval
  exact q8Cyc_ne_one hval

theorem q8CycActionE9_ne_one : q8CycActionE9 ≠ 1 := by
  intro h
  have hval : q8CycActionE9 (Multiplicative.ofAdd (1 : ZMod 3), 1) = 1 := by rw [h]; rfl
  rw [q8CycActionE9_fst_gen] at hval
  exact q8Cyc_ne_one hval

/-- `ElementaryP3 2 ≃ (ZMod 2)³`, realised concretely as a product of three copies of
`Multiplicative (ZMod 2)` (matching how `P3Group.IsP3Group` states the elementary abelian
case). -/
abbrev E8 := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

/-- The companion-matrix rotation: fixes the first coordinate, rotates the other two via
the order-`3` element `[[0,1],[1,1]]` of `GL(2,2)` (multiplication by a root of the
irreducible `x² + x + 1` over `𝔽₂`). -/
def e8RotFun : E8 → E8 := fun ⟨p, q, r⟩ => (p, r, q * r)

private def e8RotInvFun : E8 → E8 := fun ⟨p, q, r⟩ => (p, q * r, q)

private theorem e8Rot_left_inv : ∀ x : E8, e8RotInvFun (e8RotFun x) = x := by decide
private theorem e8Rot_right_inv : ∀ x : E8, e8RotFun (e8RotInvFun x) = x := by decide
private theorem e8Rot_mul : ∀ x y : E8, e8RotFun (x * y) = e8RotFun x * e8RotFun y := by decide

/-- The concrete order-`3` automorphism of `(ZMod 2)³`. -/
def e8Rot : MulAut E8 where
  toFun := e8RotFun
  invFun := e8RotInvFun
  left_inv := e8Rot_left_inv
  right_inv := e8Rot_right_inv
  map_mul' := e8Rot_mul

theorem e8Rot_apply (x : E8) : e8Rot x = e8RotFun x := rfl

theorem e8Rot_pow3 : e8Rot ^ 3 = 1 := by
  apply DFunLike.ext
  intro x
  change e8Rot (e8Rot (e8Rot x)) = x
  simp only [e8Rot_apply]
  revert x
  decide

theorem e8Rot_ne_one : e8Rot ≠ 1 := by
  intro h
  have heq : e8Rot (1, Multiplicative.ofAdd (1 : ZMod 2), 1) =
      (1, Multiplicative.ofAdd (1 : ZMod 2), 1) := by rw [h]; rfl
  rw [e8Rot_apply] at heq
  simp [e8RotFun] at heq

/-- Standard nontrivial action of `C9` on `E8`, factoring through its quotient of order `3`. -/
noncomputable def e8RotActionC9 : CyclicRep 9 →* MulAut E8 :=
  zmodActionHom 9 e8Rot (by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, e8Rot_pow3, one_pow])

/-- Standard nontrivial action of `C3 × C3` on `E8`, nontrivial on the first factor. -/
noncomputable def e8RotActionE9 : ElemAbelianRep 3 →* MulAut E8 :=
  (zmodActionHom 3 e8Rot e8Rot_pow3).comp (MonoidHom.fst (CyclicRep 3) (CyclicRep 3))

@[simp] theorem e8RotActionC9_gen :
    e8RotActionC9 (Multiplicative.ofAdd (1 : ZMod 9)) = e8Rot := by
  rw [e8RotActionC9, zmodActionHom_gen]

@[simp] theorem e8RotActionE9_fst_gen :
    e8RotActionE9 (Multiplicative.ofAdd (1 : ZMod 3), 1) = e8Rot := by
  rw [e8RotActionE9]
  simp [zmodActionHom_gen]

@[simp] theorem e8RotActionE9_snd_gen :
    e8RotActionE9 (1, Multiplicative.ofAdd (1 : ZMod 3)) = 1 := by
  rw [e8RotActionE9]
  simp

theorem e8RotActionC9_ne_one : e8RotActionC9 ≠ 1 := by
  intro h
  have hval : e8RotActionC9 (Multiplicative.ofAdd (1 : ZMod 9)) = 1 := by rw [h]; rfl
  rw [e8RotActionC9_gen] at hval
  exact e8Rot_ne_one hval

theorem e8RotActionE9_ne_one : e8RotActionE9 ≠ 1 := by
  intro h
  have hval : e8RotActionE9 (Multiplicative.ofAdd (1 : ZMod 3), 1) = 1 := by rw [h]; rfl
  rw [e8RotActionE9_fst_gen] at hval
  exact e8Rot_ne_one hval

/-! ### Standard nontrivial semidirect-product representatives in the Sylow-`2`-normal branch. -/

/-- The representative `Q8 ⋊ C9` where `C9` acts through the standard order-`3`
automorphism `q8Cyc`. -/
abbrev order72_Q8_C9_cyc : Type :=
  SemidirectProduct (QuaternionGroup 2) (CyclicRep 9) q8CycActionC9

/-- The representative `Q8 ⋊ (C3 × C3)` where the first `C3` factor acts by `q8Cyc`. -/
abbrev order72_Q8_E9_cyc : Type :=
  SemidirectProduct (QuaternionGroup 2) (ElemAbelianRep 3) q8CycActionE9

/-- The representative `E8 ⋊ C9` where `C9` acts through the standard order-`3`
automorphism `e8Rot`. -/
abbrev order72_E8_C9_rot : Type :=
  SemidirectProduct E8 (CyclicRep 9) e8RotActionC9

/-- The representative `E8 ⋊ (C3 × C3)` where the first `C3` factor acts by `e8Rot`. -/
abbrev order72_E8_E9_rot : Type :=
  SemidirectProduct E8 (ElemAbelianRep 3) e8RotActionE9

theorem card_order72_Q8 : Nat.card (QuaternionGroup 2) = 8 :=
  Nat.card_eq_fintype_card.trans (by decide)

theorem card_order72_E8 : Nat.card E8 = 8 :=
  Nat.card_eq_fintype_card.trans (by decide)

theorem card_order72_C9 : Nat.card (CyclicRep 9) = 9 :=
  card_cyclicRep (by norm_num)

theorem card_order72_E9 : Nat.card (ElemAbelianRep 3) = 9 := by
  rw [card_elemAbelianRep (by norm_num : (3 : ℕ) ≠ 0)]
  norm_num

theorem card_order72_semidirect {H K : Type*} [Group H] [Group K]
    (φ : K →* MulAut H) (hH : Nat.card H = 8) (hK : Nat.card K = 9) :
    Nat.card (SemidirectProduct H K φ) = 72 := by
  rw [SemidirectProduct.card, hH, hK]

theorem card_order72_Q8_C9_cyc : Nat.card order72_Q8_C9_cyc = 72 :=
  card_order72_semidirect q8CycActionC9 card_order72_Q8 card_order72_C9

theorem card_order72_Q8_E9_cyc : Nat.card order72_Q8_E9_cyc = 72 :=
  card_order72_semidirect q8CycActionE9 card_order72_Q8 card_order72_E9

theorem card_order72_E8_C9_rot : Nat.card order72_E8_C9_rot = 72 :=
  card_order72_semidirect e8RotActionC9 card_order72_E8 card_order72_C9

theorem card_order72_E8_E9_rot : Nat.card order72_E8_E9_rot = 72 :=
  card_order72_semidirect e8RotActionE9 card_order72_E8 card_order72_E9

theorem card_order72_C9_C8_inv : Nat.card order72_C9_C8_inv = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_cyclicRep (by norm_num : (8 : ℕ) ≠ 0)]

theorem card_order72_E9_C8_neg : Nat.card order72_E9_C8_neg = 72 := by
  rw [SemidirectProduct.card, card_order72_E9, card_cyclicRep (by norm_num : (8 : ℕ) ≠ 0)]

theorem card_order72_E9_C8_reflect : Nat.card order72_E9_C8_reflect = 72 := by
  rw [SemidirectProduct.card, card_order72_E9, card_cyclicRep (by norm_num : (8 : ℕ) ≠ 0)]

theorem card_order72_E9_C8_order4 : Nat.card order72_E9_C8_order4 = 72 := by
  rw [SemidirectProduct.card, card_order72_E9, card_cyclicRep (by norm_num : (8 : ℕ) ≠ 0)]

theorem card_order72_E9_C8_order8 : Nat.card order72_E9_C8_order8 = 72 := by
  rw [SemidirectProduct.card, card_order72_E9, card_cyclicRep (by norm_num : (8 : ℕ) ≠ 0)]

theorem card_order72_H2 : Nat.card H2 = 8 := by
  rw [H2, Nat.card_prod, card_cyclicRep (by norm_num : (4 : ℕ) ≠ 0),
    card_cyclicRep (by norm_num : (2 : ℕ) ≠ 0)]

theorem card_order72_C9_H2_fstInv : Nat.card order72_C9_H2_fstInv = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_H2]

theorem card_order72_C9_H2_sndInv : Nat.card order72_C9_H2_sndInv = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_H2]

theorem card_order72_C9_H2_prodInv : Nat.card order72_C9_H2_prodInv = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_H2]

theorem card_order72_prod {H K : Type*} [Group H] [Group K]
    (hH : Nat.card H = 8) (hK : Nat.card K = 9) :
    Nat.card (H × K) = 72 := by
  rw [Nat.card_prod, hH, hK]

/-! ### Schur-Zassenhaus reduction for the Sylow-`2`-normal branch. -/

theorem order72_semidirectProduct_of_sylow_two_normal {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 2 G, (↑P : Subgroup G).Normal) :
    ∃ (N K : Subgroup G) (φ : K →* MulAut N),
      N.Normal ∧ Nat.card N = 8 ∧ Nat.card K = 9 ∧
        Nonempty (G ≃* SemidirectProduct N K φ) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 2 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := hSyl P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 8 :=
    card_sylow_two_subgroup_of_card_72 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have hcop2 : Nat.Coprime 2 (↑P0 : Subgroup G).index :=
      (show Nat.Prime 2 by norm_num).coprime_iff_not_dvd.mpr P0.not_dvd_index
    have hcop8 := hcop2.pow_left 3
    norm_num at hcop8
    exact hcop8
  obtain ⟨K, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardK : Nat.card K = 9 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card K := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 8 * Nat.card K = 8 * 9 := by
      calc
        8 * Nat.card K = 72 := h1.symm
        _ = 8 * 9 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8) h1'
  exact ⟨↑P0, K, φ, hnorm, hcardN, hcardK, ⟨e⟩⟩

/-! ### Schur-Zassenhaus reduction for the Sylow-`3`-normal branch. -/

theorem order72_semidirectProduct_of_sylow_three_normal {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    ∃ (N K : Subgroup G) (φ : K →* MulAut N),
      N.Normal ∧ Nat.card N = 9 ∧ Nat.card K = 8 ∧
        Nonempty (G ≃* SemidirectProduct N K φ) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  haveI hnorm : (↑P0 : Subgroup G).Normal := hSyl P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 9 :=
    card_sylow_three_subgroup_of_card_72 hG P0
  haveI : (↑P0 : Subgroup G).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN]
    have hcop3 : Nat.Coprime 3 (↑P0 : Subgroup G).index :=
      (show Nat.Prime 3 by norm_num).coprime_iff_not_dvd.mpr P0.not_dvd_index
    have hcop9 := hcop3.pow_left 2
    norm_num at hcop9
    exact hcop9
  obtain ⟨K, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardK : Nat.card K = 8 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card K := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    have h1' : 9 * Nat.card K = 9 * 8 := by
      calc
        9 * Nat.card K = 72 := h1.symm
        _ = 9 * 8 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 9) h1'
  exact ⟨↑P0, K, φ, hnorm, hcardN, hcardK, ⟨e⟩⟩

/-! ### Easy order-`8` targets give direct products for every order-`9` source. -/

theorem semidirect_iso_prod_of_trivial_action {H K : Type*} [Group H] [Group K]
    {φ : K →* MulAut H} (hφ : φ = 1) :
    Nonempty (SemidirectProduct H K φ ≃* H × K) :=
  ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩

theorem c8_order9_semidirect_iso_prod {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 9) (φ : K →* MulAut (Multiplicative (ZMod 8))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 8)) K φ ≃*
      Multiplicative (ZMod 8) × K) := by
  have hφ : φ = 1 := by
    apply MonoidHom.ext
    intro k
    exact mulAut_hom_trivial_of_not_three_dvd hK
      (by rw [card_mulAut_cyclicP3_two]; norm_num) φ k
  exact semidirect_iso_prod_of_trivial_action hφ

theorem h2_order9_semidirect_iso_prod {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 9) (φ : K →* MulAut H2) :
    Nonempty (SemidirectProduct H2 K φ ≃* H2 × K) := by
  have hφ : φ = 1 := by
    apply MonoidHom.ext
    intro k
    exact mulAut_hom_trivial_of_no_order_three hK
      card_mulAut_abelianP2P_two_no_order_three φ k
  exact semidirect_iso_prod_of_trivial_action hφ

theorem d4_order9_semidirect_iso_prod {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 9) (φ : K →* MulAut (DihedralGroup 4)) :
    Nonempty (SemidirectProduct (DihedralGroup 4) K φ ≃* DihedralGroup 4 × K) := by
  have hφ : φ = 1 := by
    apply MonoidHom.ext
    intro k
    exact mulAut_hom_trivial_of_no_order_three hK
      card_mulAut_dihedralGroup_four_no_order_three φ k
  exact semidirect_iso_prod_of_trivial_action hφ

section D4C9Actions

private theorem d4_hom_ext {M : Type*} [Group M] {φ ψ : DihedralGroup 4 →* M}
    (hr : φ d4d1 = ψ d4d1) (hs : φ d4d2 = ψ d4d2) : φ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases d4gen x with h | h | h | h | h | h | h | h
  · simp [h]
  · rw [h, hr]
  · rw [h, map_pow, map_pow, hr]
  · rw [h, map_pow, map_pow, hr]
  · rw [h, hs]
  · rw [h, map_mul, map_mul, hr, hs]
  · rw [h, map_mul, map_mul, map_pow, map_pow, hr, hs]
  · rw [h, map_mul, map_mul, map_pow, map_pow, hr, hs]

private noncomputable def order72_d4InvCharRot : DihedralGroup 4 →* (ZMod 9)ˣ where
  toFun
    | DihedralGroup.r i => if i = 1 ∨ i = 3 then (-1 : (ZMod 9)ˣ) else 1
    | DihedralGroup.sr i => if i = 1 ∨ i = 3 then (-1 : (ZMod 9)ˣ) else 1
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> decide

private noncomputable def order72_d4InvCharRef : DihedralGroup 4 →* (ZMod 9)ˣ where
  toFun
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => (-1 : (ZMod 9)ˣ)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> decide

private noncomputable abbrev order72_d4InvCharProd : DihedralGroup 4 →* (ZMod 9)ˣ :=
  order72_d4InvCharRot * order72_d4InvCharRef

noncomputable def order72_c9D4InvActionRot : DihedralGroup 4 →* MulAut (CyclicRep 9) :=
  (unitAutHom (p := 9)).comp order72_d4InvCharRot

noncomputable def order72_c9D4InvActionRef : DihedralGroup 4 →* MulAut (CyclicRep 9) :=
  (unitAutHom (p := 9)).comp order72_d4InvCharRef

noncomputable def order72_c9D4InvActionProd : DihedralGroup 4 →* MulAut (CyclicRep 9) :=
  (unitAutHom (p := 9)).comp order72_d4InvCharProd

@[simp] theorem order72_c9D4InvActionRot_d1 :
    order72_c9D4InvActionRot d4d1 = order72_c9InvAut := by
  simp [order72_c9D4InvActionRot, order72_d4InvCharRot, d4d1, order72_c9InvAut]

@[simp] theorem order72_c9D4InvActionRot_d2 :
    order72_c9D4InvActionRot d4d2 = 1 := by
  have hchar : order72_d4InvCharRot d4d2 = 1 := by decide
  rw [order72_c9D4InvActionRot, MonoidHom.comp_apply, hchar, map_one]

@[simp] theorem order72_c9D4InvActionRef_d1 :
    order72_c9D4InvActionRef d4d1 = 1 := by
  rw [order72_c9D4InvActionRef, MonoidHom.comp_apply]
  change unitAutHom (1 : (ZMod 9)ˣ) = 1
  rw [map_one]

@[simp] theorem order72_c9D4InvActionRef_d2 :
    order72_c9D4InvActionRef d4d2 = order72_c9InvAut := by
  simp [order72_c9D4InvActionRef, order72_d4InvCharRef, d4d2, order72_c9InvAut]

@[simp] theorem order72_c9D4InvActionProd_d1 :
    order72_c9D4InvActionProd d4d1 = order72_c9InvAut := by
  simp [order72_c9D4InvActionProd, order72_d4InvCharProd, order72_d4InvCharRot,
    order72_d4InvCharRef, d4d1, order72_c9InvAut]

@[simp] theorem order72_c9D4InvActionProd_d2 :
    order72_c9D4InvActionProd d4d2 = order72_c9InvAut := by
  have hrot : order72_d4InvCharRot d4d2 = 1 := by decide
  rw [order72_c9D4InvActionProd, MonoidHom.comp_apply]
  change unitAutHom (order72_d4InvCharRot d4d2 * order72_d4InvCharRef d4d2) =
    order72_c9InvAut
  rw [hrot, one_mul, order72_c9InvAut]
  rfl

abbrev order72_C9_D4_invRot : Type :=
  SemidirectProduct (CyclicRep 9) (DihedralGroup 4) order72_c9D4InvActionRot

abbrev order72_C9_D4_invRef : Type :=
  SemidirectProduct (CyclicRep 9) (DihedralGroup 4) order72_c9D4InvActionRef

abbrev order72_C9_D4_invProd : Type :=
  SemidirectProduct (CyclicRep 9) (DihedralGroup 4) order72_c9D4InvActionProd

theorem order72_c9_d4_action_cases (φ : DihedralGroup 4 →* MulAut (CyclicRep 9)) :
    φ = 1 ∨ φ = order72_c9D4InvActionRot ∨
      φ = order72_c9D4InvActionRef ∨ φ = order72_c9D4InvActionProd := by
  have hcard : Nat.card (DihedralGroup 4) = 8 := Nat.card_eq_fintype_card.trans (by decide)
  rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ d4d1 with hr | hr
  · rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ d4d2 with hs | hs
    · left
      apply d4_hom_ext <;> first | simpa using hr | simpa using hs
    · right; right; left
      apply d4_hom_ext <;> first | simpa using hr | simpa using hs
  · rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ d4d2 with hs | hs
    · right; left
      apply d4_hom_ext <;> first | simpa using hr | simpa using hs
    · right; right; right
      apply d4_hom_ext <;> first | simpa using hr | simpa using hs

theorem order72_c9_d4_semidirect_cases (φ : DihedralGroup 4 →* MulAut (CyclicRep 9)) :
    Nonempty (SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ ≃*
      CyclicRep 9 × DihedralGroup 4) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ ≃*
        order72_C9_D4_invRot) ∨
        Nonempty (SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ ≃*
          order72_C9_D4_invRef) ∨
          Nonempty (SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ ≃*
            order72_C9_D4_invProd) := by
  rcases order72_c9_d4_action_cases φ with hφ | hφ | hφ | hφ
  · exact Or.inl ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · exact Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨semidirectProductCongr_eq hφ⟩))

theorem order72_c9_d4_branch_cases {G : Type*} [Group G]
    {φ : DihedralGroup 4 →* MulAut (CyclicRep 9)}
    (e : G ≃* SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ) :
    Nonempty (G ≃* CyclicRep 9 × DihedralGroup 4) ∨
      Nonempty (G ≃* order72_C9_D4_invRot) ∨
        Nonempty (G ≃* order72_C9_D4_invRef) ∨
          Nonempty (G ≃* order72_C9_D4_invProd) := by
  rcases order72_c9_d4_semidirect_cases φ with h | h | h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inl ⟨e.trans eh⟩)
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨e.trans eh⟩))

private noncomputable def order72_D4_shear : DihedralGroup 4 ≃* DihedralGroup 4 where
  toFun
    | DihedralGroup.r i => DihedralGroup.r i
    | DihedralGroup.sr i => DihedralGroup.sr (i + 1)
  invFun
    | DihedralGroup.r i => DihedralGroup.r i
    | DihedralGroup.sr i => DihedralGroup.sr (i - 1)
  left_inv := by
    rintro (i | i) <;> simp
  right_inv := by
    rintro (i | i) <;> simp
  map_mul' := by
    rintro (i | i) (j | j) <;> simp [add_assoc, sub_eq_add_neg]
    · ring_nf
    · ring_nf

private theorem order72_c9D4InvActionRot_comp_shear :
    order72_c9D4InvActionRot.comp order72_D4_shear.toMonoidHom =
      order72_c9D4InvActionProd := by
  apply d4_hom_ext
  · change order72_c9D4InvActionRot (order72_D4_shear d4d1) =
      order72_c9D4InvActionProd d4d1
    rw [show order72_D4_shear d4d1 = d4d1 by rfl]
    simp
  · change order72_c9D4InvActionRot (order72_D4_shear d4d2) =
      order72_c9D4InvActionProd d4d2
    rw [show order72_D4_shear d4d2 = (DihedralGroup.sr 1 : DihedralGroup 4) by rfl,
      order72_c9D4InvActionProd_d2]
    simp [order72_c9D4InvActionRot, order72_d4InvCharRot, order72_c9InvAut]

theorem order72_C9_D4_invProd_iso_invRot :
    Nonempty (order72_C9_D4_invProd ≃* order72_C9_D4_invRot) :=
  ⟨(semidirectProductCongr_eq order72_c9D4InvActionRot_comp_shear.symm).trans
    (semidirectProductCongrAut order72_D4_shear)⟩

theorem order72_c9_d4_semidirect_cases_standard (φ : DihedralGroup 4 →* MulAut (CyclicRep 9)) :
    Nonempty (SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ ≃*
      CyclicRep 9 × DihedralGroup 4) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ ≃*
        order72_C9_D4_invRot) ∨
        Nonempty (SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ ≃*
          order72_C9_D4_invRef) := by
  rcases order72_c9_d4_semidirect_cases φ with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · obtain ⟨e⟩ := h
    obtain ⟨eh⟩ := order72_C9_D4_invProd_iso_invRot
    exact Or.inr (Or.inl ⟨e.trans eh⟩)

theorem order72_c9_d4_branch_cases_standard {G : Type*} [Group G]
    {φ : DihedralGroup 4 →* MulAut (CyclicRep 9)}
    (e : G ≃* SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ) :
    Nonempty (G ≃* CyclicRep 9 × DihedralGroup 4) ∨
      Nonempty (G ≃* order72_C9_D4_invRot) ∨
        Nonempty (G ≃* order72_C9_D4_invRef) := by
  rcases order72_c9_d4_semidirect_cases_standard φ with h | h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inl ⟨e.trans eh⟩)
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr ⟨e.trans eh⟩)

theorem card_order72_C9_D4_invRot : Nat.card order72_C9_D4_invRot = 72 := by
  rw [SemidirectProduct.card, card_order72_C9]
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_order72_C9_D4_invRef : Nat.card order72_C9_D4_invRef = 72 := by
  rw [SemidirectProduct.card, card_order72_C9]
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_order72_C9_D4_invProd : Nat.card order72_C9_D4_invProd = 72 := by
  rw [SemidirectProduct.card, card_order72_C9]
  rw [Nat.card_eq_fintype_card]
  decide

end D4C9Actions

/-- A nontrivial action cannot be identified with the trivial action by an isomorphism that
fixes both canonical semidirect-product factors.  This is the faithfulness tool needed when
separating the nontrivial representatives from direct products. -/
theorem no_fixed_factor_iso_to_trivial_action {H K : Type*} [Group H] [Group K]
    {φ : K →* MulAut H} (hφ : φ ≠ 1) :
    ¬ ∃ e : SemidirectProduct H K φ ≃* SemidirectProduct H K (1 : K →* MulAut H),
      (∀ h : H, e (SemidirectProduct.inl h) = SemidirectProduct.inl h) ∧
      (∀ k : K, e (SemidirectProduct.inr k) = SemidirectProduct.inr k) := by
  rintro ⟨e, hl, hr⟩
  have hact : φ = (1 : K →* MulAut H) :=
    semidirectProduct_action_inj (φ := φ) (ψ := (1 : K →* MulAut H)) e hl hr
  exact hφ hact

/-! ### No order-`9` automorphism of `Q8`: `f⁹ = 1 → f³ = 1`.

This rules out the image of `φ : P →* MulAut Q8` (`P` order `9`) ever hitting an order-`9`
element, leaving only order `1` or `3`; the order-`3` values are classified below by
conjugacy to `q8Cyc`.

The argument avoids computing `Nat.card (MulAut Q8)` (which would need constructing
`Aut(Q8) ≅ S₄` from scratch): the `6`-element set of order-`4` elements of `Q8` is preserved
by any automorphism, so for `f` with `f⁹ = 1`, `Function.minimalPeriod f x` (for `x` order-`4`)
divides `9` (from `f⁹ = 1`) *and* is at most `6` (the orbit `{x, f x, …}` has
`minimalPeriod` many **distinct** elements, all inside the `6`-element set) — forcing
`minimalPeriod f x ∈ {1, 3}`, hence `f³` fixes `x`. Applying this to both generators
`a 1` and `xa 0` and combining via `map_pow`/`map_mul` gives `f³ = 1` everywhere. -/

open QuaternionGroup in
/-- The `6`-element set of order-`4` elements of `Q8`. -/
private def q8Order4Set : Finset (QuaternionGroup 2) := {a 1, a 3, xa 0, xa 1, xa 2, xa 3}

private theorem q8Order4Set_card : q8Order4Set.card = 6 := by decide

private theorem q8Order4Set_mem_iff : ∀ x : QuaternionGroup 2,
    x ∈ q8Order4Set ↔ x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by decide

private theorem q8Order4Set_preserved (f : MulAut (QuaternionGroup 2)) (y : QuaternionGroup 2)
    (hy : y ∈ q8Order4Set) : f y ∈ q8Order4Set := by
  rw [q8Order4Set_mem_iff] at hy ⊢
  constructor
  · rw [← map_pow, hy.1, map_one]
  · intro hcontra
    rw [← map_pow] at hcontra
    exact hy.2 (f.injective (by rw [hcontra, map_one]))

private theorem q8_pow_apply_eq_iterate (f : MulAut (QuaternionGroup 2)) (n : ℕ)
    (x : QuaternionGroup 2) : (f ^ n) x = f^[n] x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change f ((f ^ k) x) = _
    rw [ih, Function.iterate_succ_apply']

private theorem q8_minimalPeriod_le_six (f : MulAut (QuaternionGroup 2)) (x : QuaternionGroup 2)
    (hx : x ∈ q8Order4Set) : Function.minimalPeriod f x ≤ 6 := by
  have hall : ∀ k, f^[k] x ∈ q8Order4Set := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact q8Order4Set_preserved f _ ih
  have hmaps : Set.MapsTo (fun k => f^[k] x) (Finset.range (Function.minimalPeriod f x) : Set ℕ)
      (q8Order4Set : Set (QuaternionGroup 2)) := fun k _ => hall k
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f :=
  (f : QuaternionGroup 2 → QuaternionGroup 2))
    (x := x)
  have hinj' : ((Finset.range (Function.minimalPeriod f x) : Set ℕ)).InjOn
      (fun k => f^[k] x) := by rwa [Finset.coe_range]
  have hcard := Finset.card_le_card_of_injOn (fun k => f^[k] x) hmaps hinj'
  rwa [Finset.card_range, q8Order4Set_card] at hcard

private theorem q8_fixed_by_pow3_of_order4 (f : MulAut (QuaternionGroup 2)) (hf9 : f ^ 9 = 1)
    (x : QuaternionGroup 2) (hx : x ∈ q8Order4Set) : (f ^ 3) x = x := by
  have hperiodic9 : Function.IsPeriodicPt (⇑f) 9 x := by
    change f^[9] x = x
    rw [← q8_pow_apply_eq_iterate, hf9]
    rfl
  have hdvd9 : Function.minimalPeriod (⇑f) x ∣ 9 := hperiodic9.minimalPeriod_dvd
  have hle6 : Function.minimalPeriod (⇑f) x ≤ 6 := q8_minimalPeriod_le_six f x hx
  have hdvd3 : Function.minimalPeriod (⇑f) x ∣ 3 := by
    interval_cases h : Function.minimalPeriod (⇑f) x <;> omega
  have hp3 : Function.IsPeriodicPt (⇑f) 3 x :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hdvd3
  rw [q8_pow_apply_eq_iterate]
  exact hp3

open QuaternionGroup in
private theorem q8_natCast_val : ∀ i : ZMod 4, ((i.val : ℕ) : ZMod 4) = i := by decide

open QuaternionGroup in
private theorem q8_a_eq_a_one_pow (i : ZMod 4) : (a i : QuaternionGroup 2) = (a 1) ^ i.val := by
  rw [a_one_pow, q8_natCast_val]

open QuaternionGroup in
private theorem q8_xa_eq_xa_zero_mul (i : ZMod 4) :
    (xa i : QuaternionGroup 2) = xa 0 * a i := by rw [xa_mul_a, zero_add]

open QuaternionGroup in
/-- No automorphism of `Q8` has order `9`: `f⁹ = 1` forces `f³ = 1`. -/
theorem q8_pow9_imp_pow3 (f : MulAut (QuaternionGroup 2)) (hf9 : f ^ 9 = 1) : f ^ 3 = 1 := by
  have h1 : (f ^ 3) (a 1) = a 1 := q8_fixed_by_pow3_of_order4 f hf9 (a 1) (by decide)
  have h2 : (f ^ 3) (xa 0) = xa 0 := q8_fixed_by_pow3_of_order4 f hf9 (xa 0) (by decide)
  apply DFunLike.ext
  intro x
  change (f ^ 3) x = x
  rcases x with i | i
  · rw [q8_a_eq_a_one_pow i, map_pow, h1, ← q8_a_eq_a_one_pow]
  · rw [q8_xa_eq_xa_zero_mul i, map_mul, h2, q8_a_eq_a_one_pow i, map_pow, h1,
      ← q8_a_eq_a_one_pow, ← q8_xa_eq_xa_zero_mul]

/-! ### No order-`9` automorphism of `(ZMod 2)³` either: `f⁹ = 1 → f³ = 1`.

Same technique as `Q8`, but since `(ZMod 2)³` is elementary abelian, *every* nonidentity
element has order `2` (no order-`4` elements to single out), so instead we track all `3`
generators through the `7`-element set of *all* nonidentity elements (`7 < 9`, still enough
to force `minimalPeriod ≤ 7`, hence `∈ {1, 3}`, exactly as before). -/

private def e8NonId : Finset E8 := Finset.univ.erase 1

private theorem e8NonId_card : e8NonId.card = 7 := by decide

private theorem e8NonId_mem_iff : ∀ x : E8, x ∈ e8NonId ↔ x ≠ 1 := by decide

private theorem e8NonId_preserved (f : MulAut E8) (y : E8) (hy : y ∈ e8NonId) :
    f y ∈ e8NonId := by
  rw [e8NonId_mem_iff] at hy ⊢
  intro hcontra
  exact hy (f.injective (by rw [hcontra, map_one]))

private theorem e8_pow_apply_eq_iterate (f : MulAut E8) (n : ℕ) (x : E8) :
    (f ^ n) x = f^[n] x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change f ((f ^ k) x) = _
    rw [ih, Function.iterate_succ_apply']

private theorem e8_minimalPeriod_le_seven (f : MulAut E8) (x : E8) (hx : x ∈ e8NonId) :
    Function.minimalPeriod f x ≤ 7 := by
  have hall : ∀ k, f^[k] x ∈ e8NonId := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact e8NonId_preserved f _ ih
  have hmaps : Set.MapsTo (fun k => f^[k] x) (Finset.range (Function.minimalPeriod f x) : Set ℕ)
      (e8NonId : Set E8) := fun k _ => hall k
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := (f : E8 → E8)) (x := x)
  have hinj' : ((Finset.range (Function.minimalPeriod f x) : Set ℕ)).InjOn
      (fun k => f^[k] x) := by rwa [Finset.coe_range]
  have hcard := Finset.card_le_card_of_injOn (fun k => f^[k] x) hmaps hinj'
  rwa [Finset.card_range, e8NonId_card] at hcard

private theorem e8_fixed_by_pow3_of_nonId (f : MulAut E8) (hf9 : f ^ 9 = 1) (x : E8)
    (hx : x ∈ e8NonId) : (f ^ 3) x = x := by
  have hperiodic9 : Function.IsPeriodicPt (⇑f) 9 x := by
    change f^[9] x = x
    rw [← e8_pow_apply_eq_iterate, hf9]
    rfl
  have hdvd9 : Function.minimalPeriod (⇑f) x ∣ 9 := hperiodic9.minimalPeriod_dvd
  have hle7 : Function.minimalPeriod (⇑f) x ≤ 7 := e8_minimalPeriod_le_seven f x hx
  have hdvd3 : Function.minimalPeriod (⇑f) x ∣ 3 := by
    interval_cases h : Function.minimalPeriod (⇑f) x <;> omega
  have hp3 : Function.IsPeriodicPt (⇑f) 3 x :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hdvd3
  rw [e8_pow_apply_eq_iterate]
  exact hp3

private def e8g1 : E8 := (Multiplicative.ofAdd (1 : ZMod 2), 1, 1)
private def e8g2 : E8 := (1, Multiplicative.ofAdd (1 : ZMod 2), 1)
private def e8g3 : E8 := (1, 1, Multiplicative.ofAdd (1 : ZMod 2))

private theorem e8gen : ∀ x : E8, x = 1 ∨ x = e8g1 ∨ x = e8g2 ∨ x = e8g3 ∨ x = e8g1 * e8g2 ∨
    x = e8g1 * e8g3 ∨ x = e8g2 * e8g3 ∨ x = e8g1 * e8g2 * e8g3 := by decide

private theorem e8_hom_ext {M : Type*} [Group M] {φ ψ : E8 →* M}
    (h1 : φ e8g1 = ψ e8g1) (h2 : φ e8g2 = ψ e8g2) (h3 : φ e8g3 = ψ e8g3) :
    φ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases e8gen x with h | h | h | h | h | h | h | h <;>
    simp [h, map_mul, h1, h2, h3]

private noncomputable def order72_e8InvChar (b1 b2 b3 : Bool) : E8 →* (ZMod 9)ˣ where
  toFun := fun ⟨p, q, r⟩ =>
    (if b1 && p ≠ 1 then (-1 : (ZMod 9)ˣ) else 1) *
      (if b2 && q ≠ 1 then (-1 : (ZMod 9)ˣ) else 1) *
        (if b3 && r ≠ 1 then (-1 : (ZMod 9)ˣ) else 1)
  map_one' := by
    fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> decide
  map_mul' := by
    fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> decide

noncomputable def order72_c9E8InvAction (b1 b2 b3 : Bool) : E8 →* MulAut (CyclicRep 9) :=
  (unitAutHom (p := 9)).comp (order72_e8InvChar b1 b2 b3)

@[simp] theorem order72_c9E8InvAction_e8g1 (b1 b2 b3 : Bool) :
    order72_c9E8InvAction b1 b2 b3 e8g1 = if b1 then order72_c9InvAut else 1 := by
  fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    simp [order72_c9E8InvAction, order72_e8InvChar, e8g1, order72_c9InvAut]

@[simp] theorem order72_c9E8InvAction_e8g2 (b1 b2 b3 : Bool) :
    order72_c9E8InvAction b1 b2 b3 e8g2 = if b2 then order72_c9InvAut else 1 := by
  fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    simp [order72_c9E8InvAction, order72_e8InvChar, e8g2, order72_c9InvAut]

@[simp] theorem order72_c9E8InvAction_e8g3 (b1 b2 b3 : Bool) :
    order72_c9E8InvAction b1 b2 b3 e8g3 = if b3 then order72_c9InvAut else 1 := by
  fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    simp [order72_c9E8InvAction, order72_e8InvChar, e8g3, order72_c9InvAut]

abbrev order72_C9_E8_inv100 : Type :=
  SemidirectProduct (CyclicRep 9) E8 (order72_c9E8InvAction true false false)

abbrev order72_C9_E8_inv010 : Type :=
  SemidirectProduct (CyclicRep 9) E8 (order72_c9E8InvAction false true false)

abbrev order72_C9_E8_inv001 : Type :=
  SemidirectProduct (CyclicRep 9) E8 (order72_c9E8InvAction false false true)

abbrev order72_C9_E8_inv110 : Type :=
  SemidirectProduct (CyclicRep 9) E8 (order72_c9E8InvAction true true false)

abbrev order72_C9_E8_inv101 : Type :=
  SemidirectProduct (CyclicRep 9) E8 (order72_c9E8InvAction true false true)

abbrev order72_C9_E8_inv011 : Type :=
  SemidirectProduct (CyclicRep 9) E8 (order72_c9E8InvAction false true true)

abbrev order72_C9_E8_inv111 : Type :=
  SemidirectProduct (CyclicRep 9) E8 (order72_c9E8InvAction true true true)

private def e8First010 : MulAut E8 where
  toFun := fun ⟨p, q, r⟩ => (q, p, r)
  invFun := fun ⟨p, q, r⟩ => (q, p, r)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

private def e8First001 : MulAut E8 where
  toFun := fun ⟨p, q, r⟩ => (r, q, p)
  invFun := fun ⟨p, q, r⟩ => (r, q, p)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

private def e8First110 : MulAut E8 where
  toFun := fun ⟨p, q, r⟩ => (p * q, q, r)
  invFun := fun ⟨p, q, r⟩ => (p * q, q, r)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

private def e8First101 : MulAut E8 where
  toFun := fun ⟨p, q, r⟩ => (p * r, q, r)
  invFun := fun ⟨p, q, r⟩ => (p * r, q, r)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

private def e8First011 : MulAut E8 where
  toFun := fun ⟨p, q, r⟩ => (q * r, p, r)
  invFun := fun ⟨p, q, r⟩ => (q, p * r, r)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

private def e8First111 : MulAut E8 where
  toFun := fun ⟨p, q, r⟩ => (p * q * r, q, r)
  invFun := fun ⟨p, q, r⟩ => (p * q * r, q, r)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

private theorem order72_c9E8InvAction_comp_010 :
    (order72_c9E8InvAction true false false).comp e8First010.toMonoidHom =
      order72_c9E8InvAction false true false := by
  apply e8_hom_ext <;>
    simp [order72_c9E8InvAction, order72_e8InvChar, e8First010, e8g1, e8g2, e8g3]

private theorem order72_c9E8InvAction_comp_001 :
    (order72_c9E8InvAction true false false).comp e8First001.toMonoidHom =
      order72_c9E8InvAction false false true := by
  apply e8_hom_ext <;>
    simp [order72_c9E8InvAction, order72_e8InvChar, e8First001, e8g1, e8g2, e8g3]

private theorem order72_c9E8InvAction_comp_110 :
    (order72_c9E8InvAction true false false).comp e8First110.toMonoidHom =
      order72_c9E8InvAction true true false := by
  apply e8_hom_ext <;>
    simp [order72_c9E8InvAction, order72_e8InvChar, e8First110, e8g1, e8g2, e8g3]

private theorem order72_c9E8InvAction_comp_101 :
    (order72_c9E8InvAction true false false).comp e8First101.toMonoidHom =
      order72_c9E8InvAction true false true := by
  apply e8_hom_ext <;>
    simp [order72_c9E8InvAction, order72_e8InvChar, e8First101, e8g1, e8g2, e8g3]

private theorem order72_c9E8InvAction_comp_011 :
    (order72_c9E8InvAction true false false).comp e8First011.toMonoidHom =
      order72_c9E8InvAction false true true := by
  apply e8_hom_ext <;>
    simp [order72_c9E8InvAction, order72_e8InvChar, e8First011, e8g1, e8g2, e8g3]

private theorem order72_c9E8InvAction_comp_111 :
    (order72_c9E8InvAction true false false).comp e8First111.toMonoidHom =
      order72_c9E8InvAction true true true := by
  apply e8_hom_ext <;>
    simp [order72_c9E8InvAction, order72_e8InvChar, e8First111, e8g1, e8g2, e8g3]

theorem order72_C9_E8_inv010_iso_inv100 :
    Nonempty (order72_C9_E8_inv010 ≃* order72_C9_E8_inv100) :=
  ⟨(semidirectProductCongr_eq order72_c9E8InvAction_comp_010.symm).trans
    (semidirectProductCongrAut e8First010)⟩

theorem order72_C9_E8_inv001_iso_inv100 :
    Nonempty (order72_C9_E8_inv001 ≃* order72_C9_E8_inv100) :=
  ⟨(semidirectProductCongr_eq order72_c9E8InvAction_comp_001.symm).trans
    (semidirectProductCongrAut e8First001)⟩

theorem order72_C9_E8_inv110_iso_inv100 :
    Nonempty (order72_C9_E8_inv110 ≃* order72_C9_E8_inv100) :=
  ⟨(semidirectProductCongr_eq order72_c9E8InvAction_comp_110.symm).trans
    (semidirectProductCongrAut e8First110)⟩

theorem order72_C9_E8_inv101_iso_inv100 :
    Nonempty (order72_C9_E8_inv101 ≃* order72_C9_E8_inv100) :=
  ⟨(semidirectProductCongr_eq order72_c9E8InvAction_comp_101.symm).trans
    (semidirectProductCongrAut e8First101)⟩

theorem order72_C9_E8_inv011_iso_inv100 :
    Nonempty (order72_C9_E8_inv011 ≃* order72_C9_E8_inv100) :=
  ⟨(semidirectProductCongr_eq order72_c9E8InvAction_comp_011.symm).trans
    (semidirectProductCongrAut e8First011)⟩

theorem order72_C9_E8_inv111_iso_inv100 :
    Nonempty (order72_C9_E8_inv111 ≃* order72_C9_E8_inv100) :=
  ⟨(semidirectProductCongr_eq order72_c9E8InvAction_comp_111.symm).trans
    (semidirectProductCongrAut e8First111)⟩

theorem order72_c9_e8_action_cases (φ : E8 →* MulAut (CyclicRep 9)) :
    φ = 1 ∨
      φ = order72_c9E8InvAction true false false ∨
      φ = order72_c9E8InvAction false true false ∨
      φ = order72_c9E8InvAction false false true ∨
      φ = order72_c9E8InvAction true true false ∨
      φ = order72_c9E8InvAction true false true ∨
      φ = order72_c9E8InvAction false true true ∨
      φ = order72_c9E8InvAction true true true := by
  have hcard : Nat.card E8 = 8 := Nat.card_eq_fintype_card.trans (by decide)
  rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ e8g1 with h1 | h1
  · rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ e8g2 with h2 | h2
    · rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ e8g3 with h3 | h3
      · left
        apply e8_hom_ext <;> first | simpa using h1 | simpa using h2 | simpa using h3
      · right; right; right; left
        apply e8_hom_ext <;> first | simpa using h1 | simpa using h2 | simpa using h3
    · rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ e8g3 with h3 | h3
      · right; right; left
        apply e8_hom_ext <;> first | simpa using h1 | simpa using h2 | simpa using h3
      · right; right; right; right; right; right; left
        apply e8_hom_ext <;> first | simpa using h1 | simpa using h2 | simpa using h3
  · rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ e8g2 with h2 | h2
    · rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ e8g3 with h3 | h3
      · right; left
        apply e8_hom_ext <;> first | simpa using h1 | simpa using h2 | simpa using h3
      · right; right; right; right; right; left
        apply e8_hom_ext <;> first | simpa using h1 | simpa using h2 | simpa using h3
    · rcases order72_c9_action_value_one_or_inv_of_card_eight hcard φ e8g3 with h3 | h3
      · right; right; right; right; left
        apply e8_hom_ext <;> first | simpa using h1 | simpa using h2 | simpa using h3
      · right; right; right; right; right; right; right
        apply e8_hom_ext <;> first | simpa using h1 | simpa using h2 | simpa using h3

theorem order72_c9_e8_semidirect_cases (φ : E8 →* MulAut (CyclicRep 9)) :
    Nonempty (SemidirectProduct (CyclicRep 9) E8 φ ≃* CyclicRep 9 × E8) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) E8 φ ≃* order72_C9_E8_inv100) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) E8 φ ≃* order72_C9_E8_inv010) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) E8 φ ≃* order72_C9_E8_inv001) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) E8 φ ≃* order72_C9_E8_inv110) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) E8 φ ≃* order72_C9_E8_inv101) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) E8 φ ≃* order72_C9_E8_inv011) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) E8 φ ≃* order72_C9_E8_inv111) := by
  rcases order72_c9_e8_action_cases φ with hφ | hφ | hφ | hφ | hφ | hφ | hφ | hφ
  · exact Or.inl ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · exact Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩)))))
  · exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩))))))
  · exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨semidirectProductCongr_eq hφ⟩))))))

theorem order72_c9_e8_branch_cases {G : Type*} [Group G] {φ : E8 →* MulAut (CyclicRep 9)}
    (e : G ≃* SemidirectProduct (CyclicRep 9) E8 φ) :
    Nonempty (G ≃* CyclicRep 9 × E8) ∨
      Nonempty (G ≃* order72_C9_E8_inv100) ∨
      Nonempty (G ≃* order72_C9_E8_inv010) ∨
      Nonempty (G ≃* order72_C9_E8_inv001) ∨
      Nonempty (G ≃* order72_C9_E8_inv110) ∨
      Nonempty (G ≃* order72_C9_E8_inv101) ∨
      Nonempty (G ≃* order72_C9_E8_inv011) ∨
      Nonempty (G ≃* order72_C9_E8_inv111) := by
  rcases order72_c9_e8_semidirect_cases φ with h | h | h | h | h | h | h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inl ⟨e.trans eh⟩)
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩)))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩)))))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))))))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans eh⟩))))))

theorem order72_c9_e8_semidirect_cases_standard (φ : E8 →* MulAut (CyclicRep 9)) :
    Nonempty (SemidirectProduct (CyclicRep 9) E8 φ ≃* CyclicRep 9 × E8) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) E8 φ ≃* order72_C9_E8_inv100) := by
  rcases order72_c9_e8_semidirect_cases φ with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨e⟩ := h
    obtain ⟨eh⟩ := order72_C9_E8_inv010_iso_inv100
    exact Or.inr ⟨e.trans eh⟩
  · obtain ⟨e⟩ := h
    obtain ⟨eh⟩ := order72_C9_E8_inv001_iso_inv100
    exact Or.inr ⟨e.trans eh⟩
  · obtain ⟨e⟩ := h
    obtain ⟨eh⟩ := order72_C9_E8_inv110_iso_inv100
    exact Or.inr ⟨e.trans eh⟩
  · obtain ⟨e⟩ := h
    obtain ⟨eh⟩ := order72_C9_E8_inv101_iso_inv100
    exact Or.inr ⟨e.trans eh⟩
  · obtain ⟨e⟩ := h
    obtain ⟨eh⟩ := order72_C9_E8_inv011_iso_inv100
    exact Or.inr ⟨e.trans eh⟩
  · obtain ⟨e⟩ := h
    obtain ⟨eh⟩ := order72_C9_E8_inv111_iso_inv100
    exact Or.inr ⟨e.trans eh⟩

theorem order72_c9_e8_branch_cases_standard {G : Type*} [Group G]
    {φ : E8 →* MulAut (CyclicRep 9)}
    (e : G ≃* SemidirectProduct (CyclicRep 9) E8 φ) :
    Nonempty (G ≃* CyclicRep 9 × E8) ∨ Nonempty (G ≃* order72_C9_E8_inv100) := by
  rcases order72_c9_e8_semidirect_cases_standard φ with h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr ⟨e.trans eh⟩

theorem card_order72_C9_E8_inv100 : Nat.card order72_C9_E8_inv100 = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_E8]

theorem card_order72_C9_E8_inv010 : Nat.card order72_C9_E8_inv010 = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_E8]

theorem card_order72_C9_E8_inv001 : Nat.card order72_C9_E8_inv001 = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_E8]

theorem card_order72_C9_E8_inv110 : Nat.card order72_C9_E8_inv110 = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_E8]

theorem card_order72_C9_E8_inv101 : Nat.card order72_C9_E8_inv101 = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_E8]

theorem card_order72_C9_E8_inv011 : Nat.card order72_C9_E8_inv011 = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_E8]

theorem card_order72_C9_E8_inv111 : Nat.card order72_C9_E8_inv111 = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_E8]

/-- No automorphism of `(ZMod 2)³` has order `9`: `f⁹ = 1` forces `f³ = 1`. -/
theorem e8_pow9_imp_pow3 (f : MulAut E8) (hf9 : f ^ 9 = 1) : f ^ 3 = 1 := by
  have h1 : (f ^ 3) e8g1 = e8g1 := e8_fixed_by_pow3_of_nonId f hf9 e8g1 (by decide)
  have h2 : (f ^ 3) e8g2 = e8g2 := e8_fixed_by_pow3_of_nonId f hf9 e8g2 (by decide)
  have h3 : (f ^ 3) e8g3 = e8g3 := e8_fixed_by_pow3_of_nonId f hf9 e8g3 (by decide)
  apply DFunLike.ext
  intro x
  change (f ^ 3) x = x
  rcases e8gen x with h | h | h | h | h | h | h | h <;>
    simp [h, map_mul, h1, h2, h3]

/-! ### Toward exhaustiveness for `Q8`: no order-`3` automorphism fixes the "axis" `a 1`
(nor sends it to `a 1⁻¹ = a 3`).

This is the first real step of the conjugacy-classification of order-`3` automorphisms of
`Q8` (classically: `Aut(Q8) ≅ S₄` acts on the three antipodal pairs `{±i,±j,±k}` as `S₃`, and
an order-`3` element of `S₄` must act on those three pairs as a genuine `3`-cycle — it cannot
fix a pair). Both halves are proved directly by generator-orbit tracking through `f`, `f²`,
`f³ = 1`, with no automorphism-group search. -/

open QuaternionGroup in
private theorem q8order4_mem : ∀ x : QuaternionGroup 2, x ^ 4 = 1 → x ^ 2 ≠ 1 →
    (x = a 1 ∨ x = a 3 ∨ x = xa 0 ∨ x = xa 1 ∨ x = xa 2 ∨ x = xa 3) := by decide

open QuaternionGroup in
private theorem q8gen : ∀ x : QuaternionGroup 2, x = 1 ∨ x = a 1 ∨ x = a 1 ^ 2 ∨ x = a 1 ^ 3 ∨
    x = xa 0 ∨ x = xa 0 * a 1 ∨ x = xa 0 * a 1 ^ 2 ∨ x = xa 0 * a 1 ^ 3 := by decide

open QuaternionGroup in
private theorem q8_xa1_eq : (xa 1 : QuaternionGroup 2) = xa 0 * a 1 := by decide
open QuaternionGroup in
private theorem q8_xa2_eq : (xa 2 : QuaternionGroup 2) = xa 0 * a 1 ^ 2 := by decide
open QuaternionGroup in
private theorem q8_xa3_eq : (xa 3 : QuaternionGroup 2) = xa 0 * a 1 ^ 3 := by decide

open QuaternionGroup in
private theorem q8calc1 : xa 0 * a 1 * a 1 = xa 0 * (a 1 : QuaternionGroup 2) ^ 2 := by decide
open QuaternionGroup in
private theorem q8calc2 : xa 0 * a 1 * a 1 ^ 2 = xa 0 * (a 1 : QuaternionGroup 2) ^ 3 := by decide
open QuaternionGroup in
private theorem q8calc3 : xa 0 * a 1 ^ 2 * a 1 ^ 2 = (xa 0 : QuaternionGroup 2) := by decide
open QuaternionGroup in
private theorem q8calc4 : xa 0 * a 1 ^ 3 * a 1 ^ 3 = xa 0 * (a 1 : QuaternionGroup 2) ^ 2 := by
  decide
open QuaternionGroup in
private theorem q8calc5 : xa 0 * a 1 ^ 3 * a 1 ^ 2 = xa 0 * (a 1 : QuaternionGroup 2) := by decide

section Q8C9Actions

open QuaternionGroup

private theorem q8_hom_ext {M : Type*} [Group M] {φ ψ : QuaternionGroup 2 →* M}
    (ha : φ (a 1) = ψ (a 1)) (hx : φ (xa 0) = ψ (xa 0)) : φ = ψ := by
  apply MonoidHom.ext
  intro x
  rcases q8gen x with h | h | h | h | h | h | h | h
  · simp [h]
  · rw [h, ha]
  · rw [h, map_pow, map_pow, ha]
  · rw [h, map_pow, map_pow, ha]
  · rw [h, hx]
  · rw [h, map_mul, map_mul, hx, ha]
  · rw [h, map_mul, map_mul, map_pow, map_pow, hx, ha]
  · rw [h, map_mul, map_mul, map_pow, map_pow, hx, ha]

private noncomputable def order72_q8InvCharA : QuaternionGroup 2 →* (ZMod 9)ˣ where
  toFun
    | a i => if i = 1 ∨ i = 3 then (-1 : (ZMod 9)ˣ) else 1
    | xa i => if i = 1 ∨ i = 3 then (-1 : (ZMod 9)ˣ) else 1
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> decide

private noncomputable def order72_q8InvCharX : QuaternionGroup 2 →* (ZMod 9)ˣ where
  toFun
    | a _ => 1
    | xa _ => (-1 : (ZMod 9)ˣ)
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> decide

private noncomputable abbrev order72_q8InvCharProd : QuaternionGroup 2 →* (ZMod 9)ˣ :=
  order72_q8InvCharA * order72_q8InvCharX

noncomputable def order72_c9Q8InvActionA : QuaternionGroup 2 →* MulAut (CyclicRep 9) :=
  (unitAutHom (p := 9)).comp order72_q8InvCharA

noncomputable def order72_c9Q8InvActionX : QuaternionGroup 2 →* MulAut (CyclicRep 9) :=
  (unitAutHom (p := 9)).comp order72_q8InvCharX

noncomputable def order72_c9Q8InvActionProd : QuaternionGroup 2 →* MulAut (CyclicRep 9) :=
  (unitAutHom (p := 9)).comp order72_q8InvCharProd

@[simp] theorem order72_c9Q8InvActionA_a1 :
    order72_c9Q8InvActionA (a 1) = order72_c9InvAut := by
  simp [order72_c9Q8InvActionA, order72_q8InvCharA, order72_c9InvAut]

@[simp] theorem order72_c9Q8InvActionA_xa0 :
    order72_c9Q8InvActionA (xa 0) = 1 := by
  have hchar : order72_q8InvCharA (xa 0) = 1 := by decide
  rw [order72_c9Q8InvActionA, MonoidHom.comp_apply, hchar, map_one]

@[simp] theorem order72_c9Q8InvActionX_a1 :
    order72_c9Q8InvActionX (a 1) = 1 := by
  rw [order72_c9Q8InvActionX, MonoidHom.comp_apply]
  change unitAutHom (1 : (ZMod 9)ˣ) = 1
  rw [map_one]

@[simp] theorem order72_c9Q8InvActionX_xa0 :
    order72_c9Q8InvActionX (xa 0) = order72_c9InvAut := by
  simp [order72_c9Q8InvActionX, order72_q8InvCharX, order72_c9InvAut]

@[simp] theorem order72_c9Q8InvActionProd_a1 :
    order72_c9Q8InvActionProd (a 1) = order72_c9InvAut := by
  simp [order72_c9Q8InvActionProd, order72_q8InvCharProd, order72_q8InvCharA,
    order72_q8InvCharX, order72_c9InvAut]

@[simp] theorem order72_c9Q8InvActionProd_xa0 :
    order72_c9Q8InvActionProd (xa 0) = order72_c9InvAut := by
  have hA : order72_q8InvCharA (xa 0) = 1 := by decide
  rw [order72_c9Q8InvActionProd, MonoidHom.comp_apply, order72_c9InvAut]
  change unitAutHom (order72_q8InvCharA (xa 0) * order72_q8InvCharX (xa 0)) =
    unitAutHom (-1 : (ZMod 9)ˣ)
  rw [hA, one_mul]
  rfl

abbrev order72_C9_Q8_invA : Type :=
  SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) order72_c9Q8InvActionA

abbrev order72_C9_Q8_invX : Type :=
  SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) order72_c9Q8InvActionX

abbrev order72_C9_Q8_invProd : Type :=
  SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) order72_c9Q8InvActionProd

theorem order72_c9_q8_action_cases (φ : QuaternionGroup 2 →* MulAut (CyclicRep 9)) :
    φ = 1 ∨ φ = order72_c9Q8InvActionA ∨
      φ = order72_c9Q8InvActionX ∨ φ = order72_c9Q8InvActionProd := by
  rcases order72_c9_action_value_one_or_inv_of_card_eight card_order72_Q8 φ (a 1) with ha | ha
  · rcases order72_c9_action_value_one_or_inv_of_card_eight card_order72_Q8 φ (xa 0) with hx | hx
    · left
      apply q8_hom_ext <;> first | simpa using ha | simpa using hx
    · right; right; left
      apply q8_hom_ext <;> first | simpa using ha | simpa using hx
  · rcases order72_c9_action_value_one_or_inv_of_card_eight card_order72_Q8 φ (xa 0) with hx | hx
    · right; left
      apply q8_hom_ext <;> first | simpa using ha | simpa using hx
    · right; right; right
      apply q8_hom_ext <;> first | simpa using ha | simpa using hx

theorem order72_c9_q8_semidirect_cases (φ : QuaternionGroup 2 →* MulAut (CyclicRep 9)) :
    Nonempty (SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ ≃*
      CyclicRep 9 × QuaternionGroup 2) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ ≃*
        order72_C9_Q8_invA) ∨
        Nonempty (SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ ≃*
          order72_C9_Q8_invX) ∨
          Nonempty (SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ ≃*
            order72_C9_Q8_invProd) := by
  rcases order72_c9_q8_action_cases φ with hφ | hφ | hφ | hφ
  · exact Or.inl ⟨(semidirectProductCongr_eq hφ).trans SemidirectProduct.mulEquivProd⟩
  · exact Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨semidirectProductCongr_eq hφ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨semidirectProductCongr_eq hφ⟩))

theorem order72_c9_q8_branch_cases {G : Type*} [Group G]
    {φ : QuaternionGroup 2 →* MulAut (CyclicRep 9)}
    (e : G ≃* SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ) :
    Nonempty (G ≃* CyclicRep 9 × QuaternionGroup 2) ∨
      Nonempty (G ≃* order72_C9_Q8_invA) ∨
        Nonempty (G ≃* order72_C9_Q8_invX) ∨
          Nonempty (G ≃* order72_C9_Q8_invProd) := by
  rcases order72_c9_q8_semidirect_cases φ with h | h | h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inl ⟨e.trans eh⟩)
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.trans eh⟩))
  · obtain ⟨eh⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨e.trans eh⟩))

private noncomputable def order72_Q8_shear : QuaternionGroup 2 ≃* QuaternionGroup 2 where
  toFun
    | a i => a i
    | xa i => xa (i + 1)
  invFun
    | a i => a i
    | xa i => xa (i - 1)
  left_inv := by
    rintro (i | i) <;> simp
  right_inv := by
    rintro (i | i) <;> simp
  map_mul' := by
    rintro (i | i) (j | j) <;> simp [add_assoc, sub_eq_add_neg]
    · ring_nf
    · ring_nf

private noncomputable def order72_Q8_swap : QuaternionGroup 2 ≃* QuaternionGroup 2 where
  toFun
    | a i => (xa (0 : ZMod 4) : QuaternionGroup 2) ^ i.val
    | xa i => (a (1 : ZMod 4) : QuaternionGroup 2) *
        (xa (0 : ZMod 4) : QuaternionGroup 2) ^ i.val
  invFun
    | a i => (xa (0 : ZMod 4) : QuaternionGroup 2) ^ i.val
    | xa i => (a (1 : ZMod 4) : QuaternionGroup 2) *
        (xa (0 : ZMod 4) : QuaternionGroup 2) ^ i.val
  left_inv := by
    rintro (i | i) <;> fin_cases i <;> decide
  right_inv := by
    rintro (i | i) <;> fin_cases i <;> decide
  map_mul' := by
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> decide

private theorem order72_c9Q8InvActionA_comp_shear :
    order72_c9Q8InvActionA.comp order72_Q8_shear.toMonoidHom =
      order72_c9Q8InvActionProd := by
  apply q8_hom_ext
  · change order72_c9Q8InvActionA (order72_Q8_shear (a 1)) =
      order72_c9Q8InvActionProd (a 1)
    rw [show order72_Q8_shear (a 1) = (a 1 : QuaternionGroup 2) by rfl]
    simp
  · change order72_c9Q8InvActionA (order72_Q8_shear (xa 0)) =
      order72_c9Q8InvActionProd (xa 0)
    rw [show order72_Q8_shear (xa 0) = (xa 1 : QuaternionGroup 2) by rfl,
      order72_c9Q8InvActionProd_xa0]
    simp [order72_c9Q8InvActionA, order72_q8InvCharA, order72_c9InvAut]

private theorem order72_c9Q8InvActionA_comp_swap :
    order72_c9Q8InvActionA.comp order72_Q8_swap.toMonoidHom =
      order72_c9Q8InvActionX := by
  apply q8_hom_ext
  · change order72_c9Q8InvActionA (order72_Q8_swap (a 1)) = order72_c9Q8InvActionX (a 1)
    rw [show order72_Q8_swap (a 1) = (xa 0 : QuaternionGroup 2) by decide]
    simp
  · change order72_c9Q8InvActionA (order72_Q8_swap (xa 0)) =
      order72_c9Q8InvActionX (xa 0)
    rw [show order72_Q8_swap (xa 0) = (a 1 : QuaternionGroup 2) by decide]
    simp

theorem order72_C9_Q8_invProd_iso_invA :
    Nonempty (order72_C9_Q8_invProd ≃* order72_C9_Q8_invA) :=
  ⟨(semidirectProductCongr_eq order72_c9Q8InvActionA_comp_shear.symm).trans
    (semidirectProductCongrAut order72_Q8_shear)⟩

theorem order72_C9_Q8_invX_iso_invA :
    Nonempty (order72_C9_Q8_invX ≃* order72_C9_Q8_invA) :=
  ⟨(semidirectProductCongr_eq order72_c9Q8InvActionA_comp_swap.symm).trans
    (semidirectProductCongrAut order72_Q8_swap)⟩

theorem order72_c9_q8_semidirect_cases_standard
    (φ : QuaternionGroup 2 →* MulAut (CyclicRep 9)) :
    Nonempty (SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ ≃*
      CyclicRep 9 × QuaternionGroup 2) ∨
      Nonempty (SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ ≃*
        order72_C9_Q8_invA) := by
  rcases order72_c9_q8_semidirect_cases φ with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨e⟩ := h
    obtain ⟨eh⟩ := order72_C9_Q8_invX_iso_invA
    exact Or.inr ⟨e.trans eh⟩
  · obtain ⟨e⟩ := h
    obtain ⟨eh⟩ := order72_C9_Q8_invProd_iso_invA
    exact Or.inr ⟨e.trans eh⟩

theorem order72_c9_q8_branch_cases_standard {G : Type*} [Group G]
    {φ : QuaternionGroup 2 →* MulAut (CyclicRep 9)}
    (e : G ≃* SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ) :
    Nonempty (G ≃* CyclicRep 9 × QuaternionGroup 2) ∨
      Nonempty (G ≃* order72_C9_Q8_invA) := by
  rcases order72_c9_q8_semidirect_cases_standard φ with h | h
  · obtain ⟨eh⟩ := h
    exact Or.inl ⟨e.trans eh⟩
  · obtain ⟨eh⟩ := h
    exact Or.inr ⟨e.trans eh⟩

theorem card_order72_C9_Q8_invA : Nat.card order72_C9_Q8_invA = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_Q8]

theorem card_order72_C9_Q8_invX : Nat.card order72_C9_Q8_invX = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_Q8]

theorem card_order72_C9_Q8_invProd : Nat.card order72_C9_Q8_invProd = 72 := by
  rw [SemidirectProduct.card, card_order72_C9, card_order72_Q8]

end Q8C9Actions

open QuaternionGroup in
/-- No order-`3` automorphism of `Q8` sends `a 1` (`= i`) to `a 3` (`= i⁻¹ = -i`). -/
theorem q8_order3_fa1_ne_a3 (f : MulAut (QuaternionGroup 2)) (hf3 : f ^ 3 = 1) :
    f (a 1) ≠ a 3 := by
  intro heq
  have hfapp : ∀ g : QuaternionGroup 2, (f ^ 3) g = g := by intro g; rw [hf3]; rfl
  have hfa3 : f (a 3) = a 1 := by
    have h13 : (a 3 : QuaternionGroup 2) = (a 1) ^ 3 := by decide
    rw [h13, map_pow, heq]; decide
  have h3 : f (f (f (a 1))) = a 1 := hfapp (a 1)
  rw [heq, hfa3, heq] at h3
  exact absurd h3 (by decide)

open QuaternionGroup in
/-- No **nontrivial** order-`3` automorphism of `Q8` fixes `a 1` (`= i`). Combined with
`q8_order3_fa1_ne_a3`, every nontrivial order-`3` `f` sends `a 1` to one of the four
`X`-type order-`4` elements `xa 0, xa 1, xa 2, xa 3`. -/
theorem q8_order3_fa1_ne_a1 (f : MulAut (QuaternionGroup 2)) (hf3 : f ^ 3 = 1)
    (hfne1 : f ≠ 1) : f (a 1) ≠ a 1 := by
  intro heq
  have hfapp : ∀ g : QuaternionGroup 2, (f ^ 3) g = g := by intro g; rw [hf3]; rfl
  have hfa3 : f (a 3) = a 3 := by
    have h13 : (a 3 : QuaternionGroup 2) = (a 1) ^ 3 := by decide
    rw [h13, map_pow, heq]
  have hxa0_4 : (f (xa 0)) ^ 4 = 1 := by
    have h1 : (xa 0 : QuaternionGroup 2) ^ 4 = 1 := by decide
    rw [← map_pow, h1, map_one]
  have hxa0_sqne1 : (f (xa 0)) ^ 2 ≠ 1 := by
    have hne : (xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
    rw [← map_pow]
    intro hc
    exact hne (f.injective (by rw [hc, map_one]))
  rcases q8order4_mem (f (xa 0)) hxa0_4 hxa0_sqne1 with h | h | h | h | h | h
  · exact absurd (f.injective (h.trans heq.symm)) (by decide)
  · exact absurd (f.injective (h.trans hfa3.symm)) (by decide)
  · apply hfne1
    have hfa2 : f (a 2) = a 2 := by
      have ha2 : (a 2 : QuaternionGroup 2) = a 1 ^ 2 := by decide
      rw [ha2, map_pow, heq]
    have hfxa1 : f (xa 1) = xa 1 := by rw [q8_xa1_eq, map_mul, h, heq]
    have hfxa2 : f (xa 2) = xa 2 := by rw [q8_xa2_eq, map_mul, map_pow, h, heq]
    have hfxa3 : f (xa 3) = xa 3 := by rw [q8_xa3_eq, map_mul, map_pow, h, heq]
    apply DFunLike.ext
    intro x
    change f x = x
    rcases q8gen x with hx | hx | hx | hx | hx | hx | hx | hx <;> rw [hx] <;>
      first
        | exact map_one f
        | exact heq
        | exact hfa2
        | exact hfa3
        | exact h
        | exact hfxa1
        | exact hfxa2
        | exact hfxa3
  · rw [q8_xa1_eq] at h
    have hf2 : f (f (xa 0)) = xa 0 * a 1 ^ 2 := by
      rw [h, map_mul, h, heq]; exact q8calc1
    have hf3' : f (f (f (xa 0))) = xa 0 * a 1 ^ 3 := by
      rw [hf2, map_mul, map_pow, h, heq]; exact q8calc2
    have hcontra : f (f (f (xa 0))) = xa 0 := hfapp (xa 0)
    rw [hf3'] at hcontra
    have heq2 : xa 0 * (a 1 : QuaternionGroup 2) ^ 3 = xa 0 * 1 := by
      rw [mul_one]; exact hcontra
    exact absurd (mul_left_cancel heq2) (by decide)
  · rw [q8_xa2_eq] at h
    have hf2 : f (f (xa 0)) = xa 0 := by
      rw [h, map_mul, h, map_pow, heq]; exact q8calc3
    have hf3' : f (f (f (xa 0))) = xa 0 * a 1 ^ 2 := by rw [hf2]; exact h
    have hcontra : f (f (f (xa 0))) = xa 0 := hfapp (xa 0)
    rw [hf3'] at hcontra
    have heq2 : xa 0 * (a 1 : QuaternionGroup 2) ^ 2 = xa 0 * 1 := by
      rw [mul_one]; exact hcontra
    exact absurd (mul_left_cancel heq2) (by decide)
  · rw [q8_xa3_eq] at h
    have hf2 : f (f (xa 0)) = xa 0 * a 1 ^ 2 := by
      rw [h, map_mul, h, map_pow, heq]; exact q8calc4
    have hf3' : f (f (f (xa 0))) = xa 0 * a 1 := by
      rw [hf2, map_mul, map_pow, h, heq]; exact q8calc5
    have hcontra : f (f (f (xa 0))) = xa 0 := hfapp (xa 0)
    rw [hf3'] at hcontra
    have heq2 : xa 0 * (a 1 : QuaternionGroup 2) = xa 0 * 1 := by
      rw [mul_one]; exact hcontra
    exact absurd (mul_left_cancel heq2) (by decide)

open QuaternionGroup in
/-- Every nontrivial order-`3` automorphism of `Q8` sends `a 1` to one of the four
`X`-type order-`4` elements. -/
theorem q8_order3_fa1_mem (f : MulAut (QuaternionGroup 2)) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    f (a 1) = xa 0 ∨ f (a 1) = xa 1 ∨ f (a 1) = xa 2 ∨ f (a 1) = xa 3 := by
  have h4 : (f (a 1)) ^ 4 = 1 := by
    have h1 : (a 1 : QuaternionGroup 2) ^ 4 = 1 := by decide
    rw [← map_pow, h1, map_one]
  have hsqne1 : (f (a 1)) ^ 2 ≠ 1 := by
    have hne : (a 1 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
    rw [← map_pow]
    intro hc
    exact hne (f.injective (by rw [hc, map_one]))
  rcases q8order4_mem (f (a 1)) h4 hsqne1 with h | h | h | h | h | h
  · exact absurd h (q8_order3_fa1_ne_a1 f hf3 hfne1)
  · exact absurd h (q8_order3_fa1_ne_a3 f hf3)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-! ### The "generation formula": every automorphism of `Q8` is determined by where it sends
the two generators `a 1` and `xa 0`, via `f (a k) = f (a 1) ^ k` and
`f (xa k) = f (xa 0) * f (a 1) ^ k`. This reduces "classify `f` up to conjugacy" to a
finite search over the (small) set of valid `(f (a 1), f (xa 0))` pairs — no automorphism-group
enumeration needed. -/

open QuaternionGroup in
private theorem q8_ak_eq : ∀ k : ZMod 4, (a k : QuaternionGroup 2) = (a 1) ^ k.val := by decide

open QuaternionGroup in
private theorem q8_xak_eq : ∀ k : ZMod 4, (xa k : QuaternionGroup 2) = xa 0 * (a 1) ^ k.val := by
  decide

open QuaternionGroup in
theorem q8_f_ak (f : MulAut (QuaternionGroup 2)) (k : ZMod 4) :
    f (a k) = (f (a 1)) ^ k.val := by rw [q8_ak_eq, map_pow]

open QuaternionGroup in
theorem q8_f_xak (f : MulAut (QuaternionGroup 2)) (k : ZMod 4) :
    f (xa k) = f (xa 0) * (f (a 1)) ^ k.val := by rw [q8_xak_eq, map_mul, map_pow]

open QuaternionGroup in
/-- The purely computational model of a `Q8`-endomorphism determined by where it sends the two
generators: `q8ext A' X'` is the function that would result from extending `a 1 ↦ A'`,
`xa 0 ↦ X'` via the generation relations. -/
private def q8ext (A' X' : QuaternionGroup 2) : QuaternionGroup 2 → QuaternionGroup 2
  | .a k => A' ^ k.val
  | .xa k => X' * A' ^ k.val

/-- Build the `MulAut` corresponding to a valid `(A', X')` pair: `q8ext A' X'` is already a
homomorphism (`hHom`, checked by a small `decide`) and injective (`hInj`, ditto), hence
bijective on the finite `Q8` — this packages it as a genuine automorphism, reusable for every
conjugator we need below (avoiding a bespoke `toFun`/`invFun` table each time, unlike `q8Cyc`).
-/
private noncomputable def q8BuildAut (A' X' : QuaternionGroup 2)
    (hHom : ∀ x y, q8ext A' X' (x * y) = q8ext A' X' x * q8ext A' X' y)
    (hInj : Function.Injective (q8ext A' X')) : MulAut (QuaternionGroup 2) :=
  MulEquiv.ofBijective (MonoidHom.mk' (q8ext A' X') hHom)
    (Finite.injective_iff_bijective.mp hInj)

private theorem q8BuildAut_apply (A' X' : QuaternionGroup 2) (hHom hInj) (x : QuaternionGroup 2) :
    q8BuildAut A' X' hHom hInj x = q8ext A' X' x := rfl

open QuaternionGroup in
/-- Every automorphism agrees with the `q8ext` model built from its own values on the two
generators. -/
private theorem q8_f_eq_ext (f : MulAut (QuaternionGroup 2)) (x : QuaternionGroup 2) :
    f x = q8ext (f (a 1)) (f (xa 0)) x := by
  cases x with
  | a k => exact q8_f_ak f k
  | xa k => exact q8_f_xak f k

open QuaternionGroup in
/-- Small closed-form computation (`4 × 6 = 24` concrete pairs, nothing like a full
automorphism-group search) pinning `f (xa 0)` once `f (a 1)` and the order-`3` condition are
known. -/
private theorem q8_pin_decide : ∀ A' X' : QuaternionGroup 2,
    (A' = xa 0 ∨ A' = xa 1 ∨ A' = xa 2 ∨ A' = xa 3) →
    (X' = a 1 ∨ X' = a 3 ∨ X' = xa 0 ∨ X' = xa 1 ∨ X' = xa 2 ∨ X' = xa 3) →
    (q8ext A' X' (q8ext A' X' (q8ext A' X' (a 1))) = a 1 ∧
     q8ext A' X' (q8ext A' X' (q8ext A' X' (xa 0))) = xa 0) →
    (A' = xa 0 ∧ (X' = xa 1 ∨ X' = xa 3)) ∨
    (A' = xa 1 ∧ (X' = a 1 ∨ X' = a 3)) ∨
    (A' = xa 2 ∧ (X' = xa 1 ∨ X' = xa 3)) ∨
    (A' = xa 3 ∧ (X' = a 1 ∨ X' = a 3)) := by decide

open QuaternionGroup in
/-- Full pin: for a nontrivial order-`3` automorphism of `Q8`, `(f (a 1), f (xa 0))` is one of
exactly eight pairs (matching the eight order-`3` elements of `Aut(Q8) ≅ S₄`). -/
theorem q8_order3_pin (f : MulAut (QuaternionGroup 2)) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    (f (a 1) = xa 0 ∧ (f (xa 0) = xa 1 ∨ f (xa 0) = xa 3)) ∨
    (f (a 1) = xa 1 ∧ (f (xa 0) = a 1 ∨ f (xa 0) = a 3)) ∨
    (f (a 1) = xa 2 ∧ (f (xa 0) = xa 1 ∨ f (xa 0) = xa 3)) ∨
    (f (a 1) = xa 3 ∧ (f (xa 0) = a 1 ∨ f (xa 0) = a 3)) := by
  have hmem := q8_order3_fa1_mem f hf3 hfne1
  have hx4 : (f (xa 0)) ^ 4 = 1 := by
    have h1 : (xa 0 : QuaternionGroup 2) ^ 4 = 1 := by decide
    rw [← map_pow, h1, map_one]
  have hxsqne1 : (f (xa 0)) ^ 2 ≠ 1 := by
    have hne : (xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
    rw [← map_pow]
    intro hc
    exact hne (f.injective (by rw [hc, map_one]))
  have hxmem := q8order4_mem (f (xa 0)) hx4 hxsqne1
  have stepx1 : q8ext (f (a 1)) (f (xa 0)) (xa 0) = f (xa 0) := (q8_f_eq_ext f (xa 0)).symm
  have stepx2 : q8ext (f (a 1)) (f (xa 0)) (f (xa 0)) = f (f (xa 0)) :=
    (q8_f_eq_ext f (f (xa 0))).symm
  have stepx3 : q8ext (f (a 1)) (f (xa 0)) (f (f (xa 0))) = f (f (f (xa 0))) :=
    (q8_f_eq_ext f (f (f (xa 0)))).symm
  have stepa1 : q8ext (f (a 1)) (f (xa 0)) (a 1) = f (a 1) := (q8_f_eq_ext f (a 1)).symm
  have stepa2 : q8ext (f (a 1)) (f (xa 0)) (f (a 1)) = f (f (a 1)) :=
    (q8_f_eq_ext f (f (a 1))).symm
  have stepa3 : q8ext (f (a 1)) (f (xa 0)) (f (f (a 1))) = f (f (f (a 1))) :=
    (q8_f_eq_ext f (f (f (a 1)))).symm
  have happx : f (f (f (xa 0))) = xa 0 := by
    have h : (f ^ 3) (xa 0) = xa 0 := by rw [hf3]; rfl
    exact h
  have happa : f (f (f (a 1))) = a 1 := by
    have h : (f ^ 3) (a 1) = a 1 := by rw [hf3]; rfl
    exact h
  have h3x : q8ext (f (a 1)) (f (xa 0)) (q8ext (f (a 1)) (f (xa 0))
      (q8ext (f (a 1)) (f (xa 0)) (xa 0))) = xa 0 := by
    rw [stepx1, stepx2, stepx3]; exact happx
  have h3a : q8ext (f (a 1)) (f (xa 0)) (q8ext (f (a 1)) (f (xa 0))
      (q8ext (f (a 1)) (f (xa 0)) (a 1))) = a 1 := by
    rw [stepa1, stepa2, stepa3]; exact happa
  exact q8_pin_decide (f (a 1)) (f (xa 0)) hmem hxmem ⟨h3a, h3x⟩

open QuaternionGroup in
private theorem q8Cyc_eq_ext (x : QuaternionGroup 2) : q8Cyc x = q8ext (xa 0) (xa 3) x := by
  have h := q8_f_eq_ext q8Cyc x
  rwa [show q8Cyc (a 1) = xa 0 from rfl, show q8Cyc (xa 0) = xa 3 from rfl] at h

open QuaternionGroup in
/-- Every nontrivial order-`3` automorphism of `Q8` is `Aut(Q8)`-conjugate to `q8Cyc`. Combined
with `q8Cyc_pow3`/`q8Cyc_ne_one`, this completes the order-`3` conjugacy classification for
`Q8`: exhaustiveness at the "genuinely new action" case of the Sylow-2-normal branch. -/
theorem q8_order3_conj_to_cyc (f : MulAut (QuaternionGroup 2)) (hf3 : f ^ 3 = 1)
    (hfne1 : f ≠ 1) : ∃ g : MulAut (QuaternionGroup 2), g * f * g⁻¹ = q8Cyc := by
  have hpin := q8_order3_pin f hf3 hfne1
  -- Given a valid conjugator `(gA, gX)` for the pinned pair `(f (a 1), f (xa 0))`, package it
  -- into the conclusion.
  suffices h : ∃ gA gX : QuaternionGroup 2,
      ∃ hHom : ∀ x y, q8ext gA gX (x * y) = q8ext gA gX x * q8ext gA gX y,
      ∃ hInj : Function.Injective (q8ext gA gX),
      ∀ x, q8ext gA gX (f x) = q8ext (xa 0) (xa 3) (q8ext gA gX x) by
    obtain ⟨gA, gX, hHom, hInj, hconj⟩ := h
    refine ⟨q8BuildAut gA gX hHom hInj, ?_⟩
    set g := q8BuildAut gA gX hHom hInj with hgdef
    apply DFunLike.ext
    intro x
    change g (f (g⁻¹ x)) = q8Cyc x
    rw [q8Cyc_eq_ext]
    have e1 : g (f (g⁻¹ x)) = q8ext gA gX (f (g⁻¹ x)) := q8BuildAut_apply gA gX hHom hInj _
    have e2 : q8ext gA gX (g⁻¹ x) = g (g⁻¹ x) := (q8BuildAut_apply gA gX hHom hInj _).symm
    have hgg : g (g⁻¹ x) = x := by simp
    rw [e1, hconj (g⁻¹ x), e2, hgg]
  rcases hpin with ⟨hA, hX | hX⟩ | ⟨hA, hX | hX⟩ | ⟨hA, hX | hX⟩ | ⟨hA, hX | hX⟩
  · -- (xa0, xa1): conjugator (xa1, a3)
    refine ⟨xa 1, a 3, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa0, xa3) = q8Cyc itself: trivial conjugator (identity)
    refine ⟨a 1, xa 0, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa1, a1): conjugator (xa0, a1)
    refine ⟨xa 0, a 1, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa1, a3): conjugator (xa1, xa0)
    refine ⟨xa 1, xa 0, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa2, xa1): conjugator (xa1, a1)
    refine ⟨xa 1, a 1, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa2, xa3): conjugator (xa0, xa1)
    refine ⟨xa 0, xa 1, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa3, a1): conjugator (xa1, xa2)
    refine ⟨xa 1, xa 2, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide
  · -- (xa3, a3) = q8Cyc²: conjugator (a1, xa1)
    refine ⟨a 1, xa 1, by decide, by decide, ?_⟩
    intro x; rw [q8_f_eq_ext f x, hA, hX]; revert x; decide

open QuaternionGroup in
/-- The order-`3` part of the centralizer of `q8Cyc` in `Aut(Q8)` is the cyclic subgroup
generated by `q8Cyc`. -/
theorem q8_commute_cyc_order3_cases (f : MulAut (QuaternionGroup 2)) (hf3 : f ^ 3 = 1)
    (hcomm : f * q8Cyc = q8Cyc * f) : f = 1 ∨ f = q8Cyc ∨ f = q8Cyc ^ 2 := by
  by_cases hf1 : f = 1
  · exact Or.inl hf1
  · right
    have hpin := q8_order3_pin f hf3 hf1
    have hcomm_ext : ∀ x : QuaternionGroup 2,
        q8ext (f (a 1)) (f (xa 0)) (q8Cyc x) =
          q8Cyc (q8ext (f (a 1)) (f (xa 0)) x) := by
      intro x
      have hx := congrArg (fun u : MulAut (QuaternionGroup 2) => u x) hcomm
      change f (q8Cyc x) = q8Cyc (f x) at hx
      rw [q8_f_eq_ext f (q8Cyc x), q8_f_eq_ext f x] at hx
      exact hx
    rcases hpin with ⟨hA, hX | hX⟩ | ⟨hA, hX | hX⟩ |
      ⟨hA, hX | hX⟩ | ⟨hA, hX | hX⟩
    · exfalso
      have hc := hcomm_ext
      rw [hA, hX] at hc
      exact (show ¬ _ from by decide) hc
    · left
      apply DFunLike.ext
      intro x
      rw [q8_f_eq_ext f x, hA, hX, q8Cyc_eq_ext]
    · exfalso
      have hc := hcomm_ext
      rw [hA, hX] at hc
      exact (show ¬ _ from by decide) hc
    · exfalso
      have hc := hcomm_ext
      rw [hA, hX] at hc
      exact (show ¬ _ from by decide) hc
    · exfalso
      have hc := hcomm_ext
      rw [hA, hX] at hc
      exact (show ¬ _ from by decide) hc
    · exfalso
      have hc := hcomm_ext
      rw [hA, hX] at hc
      exact (show ¬ _ from by decide) hc
    · right
      apply DFunLike.ext
      intro x
      rw [q8_f_eq_ext f x, hA, hX]
      change q8ext (xa 3) (a 1) x = q8Cyc (q8Cyc x)
      revert x
      decide
    · exfalso
      have hc := hcomm_ext
      rw [hA, hX] at hc
      exact (show ¬ _ from by decide) hc

/-- A nontrivial action of a group of order `9` on `Q8` contains an element whose image is
`Aut(Q8)`-conjugate to the standard `q8Cyc`. -/
theorem q8_hom_nontrivial_elem_conj_to_cyc {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 9) (φ : K →* MulAut (QuaternionGroup 2)) (hφ : φ ≠ 1) :
    ∃ k : K, φ k ≠ 1 ∧ ∃ g : MulAut (QuaternionGroup 2), g * φ k * g⁻¹ = q8Cyc := by
  have hnontriv : ∃ k : K, φ k ≠ 1 := exists_apply_ne_one_of_monoidHom_ne_one φ hφ
  obtain ⟨k, hkne⟩ := hnontriv
  have hk9 : k ^ 9 = 1 := by
    exact orderOf_dvd_iff_pow_eq_one.mp (hK ▸ orderOf_dvd_natCard k)
  have hφ9 : (φ k) ^ 9 = 1 := by
    rw [← map_pow, hk9, map_one]
  have hφ3 : (φ k) ^ 3 = 1 := q8_pow9_imp_pow3 (φ k) hφ9
  exact ⟨k, hkne, q8_order3_conj_to_cyc (φ k) hφ3 hkne⟩

/-- Every value of an action of a group of order `9` on `Q8` has cube equal to the identity. -/
theorem q8_hom_apply_pow3_of_card9 {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 9) (φ : K →* MulAut (QuaternionGroup 2)) (k : K) :
    (φ k) ^ 3 = 1 := by
  have hk9 : k ^ 9 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hK ▸ orderOf_dvd_natCard k)
  have hφ9 : (φ k) ^ 9 = 1 := by
    rw [← map_pow, hk9, map_one]
  exact q8_pow9_imp_pow3 (φ k) hφ9

/-- Pointwise form for order-`9` actions on `Q8`: each element acts trivially or by an
automorphism conjugate to `q8Cyc`. -/
theorem q8_hom_apply_eq_one_or_conj_to_cyc {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 9) (φ : K →* MulAut (QuaternionGroup 2)) (k : K) :
    φ k = 1 ∨ ∃ g : MulAut (QuaternionGroup 2), g * φ k * g⁻¹ = q8Cyc := by
  by_cases hk : φ k = 1
  · exact Or.inl hk
  · exact Or.inr (q8_order3_conj_to_cyc (φ k) (q8_hom_apply_pow3_of_card9 hK φ k) hk)

/-- Orbit-move form of `q8_hom_nontrivial_elem_conj_to_cyc`: after conjugating the whole
action by an automorphism of `Q8`, some element of the order-`9` source acts exactly as
`q8Cyc`. -/
theorem q8_hom_nontrivial_conj_has_cyc_value {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 9) (φ : K →* MulAut (QuaternionGroup 2)) (hφ : φ ≠ 1) :
    ∃ k : K, ∃ g : MulAut (QuaternionGroup 2),
      ((MulAut.conj g).toMonoidHom.comp φ) k = q8Cyc := by
  obtain ⟨k, _hkne, g, hg⟩ := q8_hom_nontrivial_elem_conj_to_cyc hK φ hφ
  exact ⟨k, g, by simpa [MonoidHom.comp_apply, MulAut.conj_apply] using hg⟩

/-- Every nontrivial `C9`-action on `Q8` is target-conjugate to the standard action. -/
theorem q8_c9_action_conj_eq_standard
    (φ : CyclicRep 9 →* MulAut (QuaternionGroup 2)) (hφ : φ ≠ 1) :
    ∃ g : MulAut (QuaternionGroup 2),
      (MulAut.conj g).toMonoidHom.comp φ = q8CycActionC9 := by
  let c : CyclicRep 9 := Multiplicative.ofAdd (1 : ZMod 9)
  have hcne : φ c ≠ 1 := by
    intro hc
    apply hφ
    apply cyclicRep_hom_ext
    simp [c, hc]
  have hc3 : (φ c) ^ 3 = 1 := q8_hom_apply_pow3_of_card9 card_order72_C9 φ c
  obtain ⟨g, hg⟩ := q8_order3_conj_to_cyc (φ c) hc3 hcne
  refine ⟨g, cyclicRep_hom_ext ?_⟩
  change (MulAut.conj g) (φ c) = q8CycActionC9 c
  simpa [c, MonoidHom.comp_apply, MulAut.conj_apply] using hg

/-- Semidirect-product form of `q8_c9_action_conj_eq_standard`. -/
theorem q8_c9_semidirect_iso_standard
    (φ : CyclicRep 9 →* MulAut (QuaternionGroup 2)) (hφ : φ ≠ 1) :
    Nonempty (SemidirectProduct (QuaternionGroup 2) (CyclicRep 9) φ ≃*
      order72_Q8_C9_cyc) := by
  obtain ⟨g, hg⟩ := q8_c9_action_conj_eq_standard φ hφ
  exact ⟨(semidirectProductCongrConj (φ := φ) g).trans (semidirectProductCongr_eq hg)⟩

/-- Actions of `C9` on `Q8` yield either the trivial semidirect product or the unique
nontrivial standard representative. -/
theorem q8_c9_semidirect_cases (φ : CyclicRep 9 →* MulAut (QuaternionGroup 2)) :
    Nonempty (SemidirectProduct (QuaternionGroup 2) (CyclicRep 9) φ ≃*
      SemidirectProduct (QuaternionGroup 2) (CyclicRep 9)
        (1 : CyclicRep 9 →* MulAut (QuaternionGroup 2))) ∨
    Nonempty (SemidirectProduct (QuaternionGroup 2) (CyclicRep 9) φ ≃*
      order72_Q8_C9_cyc) := by
  by_cases hφ : φ = 1
  · exact Or.inl ⟨semidirectProductCongr_eq hφ⟩
  · exact Or.inr (q8_c9_semidirect_iso_standard φ hφ)

/-- An `E9`-action on `Q8` with the standard values on the two generators is the standard
action. -/
theorem q8_e9_action_eq_standard_of_gen_values
    (φ : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2))
    (h1 : φ order72_E9_g1 = q8Cyc) (h2 : φ order72_E9_g2 = 1) :
    φ = q8CycActionE9 := by
  apply elemAbelianRep3_hom_ext
  · simpa [order72_E9_g1] using h1
  · simpa [order72_E9_g2] using h2

/-- Source-normalized form for the standard nontrivial `E9`-action on `Q8`. -/
theorem q8_e9_action_precomp_eq_standard
    (φ : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2))
    (σ : ElemAbelianRep 3 ≃* ElemAbelianRep 3)
    (h1 : φ (σ order72_E9_g1) = q8Cyc) (h2 : φ (σ order72_E9_g2) = 1) :
    φ.comp σ.toMonoidHom = q8CycActionE9 :=
  q8_e9_action_eq_standard_of_gen_values (φ.comp σ.toMonoidHom) h1 h2

/-- If an `E9`-action on `Q8` becomes standard after target conjugation and a source
automorphism, then its semidirect product is the standard `Q8 ⋊ E9` representative. -/
theorem q8_e9_semidirect_iso_standard_of_conj_precomp
    (φ : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2)) (g : MulAut (QuaternionGroup 2))
    (σ : ElemAbelianRep 3 ≃* ElemAbelianRep 3)
    (h1 : ((MulAut.conj g).toMonoidHom.comp φ) (σ order72_E9_g1) = q8Cyc)
    (h2 : ((MulAut.conj g).toMonoidHom.comp φ) (σ order72_E9_g2) = 1) :
    Nonempty (SemidirectProduct (QuaternionGroup 2) (ElemAbelianRep 3) φ ≃*
      order72_Q8_E9_cyc) := by
  let φ' : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2) := (MulAut.conj g).toMonoidHom.comp φ
  have hstd : φ'.comp σ.toMonoidHom = q8CycActionE9 :=
    q8_e9_action_precomp_eq_standard φ' σ h1 h2
  exact ⟨(semidirectProductCongrConj (φ := φ) g).trans
    ((semidirectProductCongrAut (φ := φ') σ).symm.trans (semidirectProductCongr_eq hstd))⟩

/-- If the first generator of `E9` acts by `q8Cyc`, then the whole `E9`-action on `Q8`
is equivalent to the standard representative.  The second generator is forced into the
cyclic centralizer of `q8Cyc`, and a source shear removes it. -/
theorem q8_e9_semidirect_iso_standard_of_first_gen
    (φ : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2))
    (h1 : φ order72_E9_g1 = q8Cyc) :
    Nonempty (SemidirectProduct (QuaternionGroup 2) (ElemAbelianRep 3) φ ≃*
      order72_Q8_E9_cyc) := by
  have hcomm : φ order72_E9_g2 * q8Cyc = q8Cyc * φ order72_E9_g2 := by
    have hsrc : order72_E9_g2 * order72_E9_g1 = order72_E9_g1 * order72_E9_g2 := by
      ext <;> simp [order72_E9_g1, order72_E9_g2, mul_comm]
    calc
      φ order72_E9_g2 * q8Cyc = φ order72_E9_g2 * φ order72_E9_g1 := by rw [h1]
      _ = φ (order72_E9_g2 * order72_E9_g1) := by rw [map_mul]
      _ = φ (order72_E9_g1 * order72_E9_g2) := by rw [hsrc]
      _ = φ order72_E9_g1 * φ order72_E9_g2 := by rw [map_mul]
      _ = q8Cyc * φ order72_E9_g2 := by rw [h1]
  have hpow : (φ order72_E9_g2) ^ 3 = 1 :=
    q8_hom_apply_pow3_of_card9 card_order72_E9 φ order72_E9_g2
  rcases q8_commute_cyc_order3_cases (φ order72_E9_g2) hpow hcomm with h2 | h2 | h2
  · exact q8_e9_semidirect_iso_standard_of_conj_precomp φ 1 (MulEquiv.refl _) (by
      simpa [MonoidHom.comp_apply, MulAut.conj_apply] using h1) (by
      simpa [MonoidHom.comp_apply, MulAut.conj_apply] using h2)
  · exact q8_e9_semidirect_iso_standard_of_conj_precomp φ 1 order72_E9_shearPlus.symm (by
      simpa [MonoidHom.comp_apply, MulAut.conj_apply, order72_E9_shearMinus_g1] using h1) (by
      change φ (order72_E9_shearPlus.symm order72_E9_g2) = 1
      rw [order72_E9_shearMinus_g2, map_mul, map_pow, h1, h2]
      calc
        q8Cyc ^ 2 * q8Cyc = q8Cyc ^ 3 := by group
        _ = 1 := q8Cyc_pow3)
  · exact q8_e9_semidirect_iso_standard_of_conj_precomp φ 1 order72_E9_shearPlus (by
      simpa [MonoidHom.comp_apply, MulAut.conj_apply, order72_E9_shearPlus_g1] using h1) (by
      change φ (order72_E9_shearPlus order72_E9_g2) = 1
      rw [order72_E9_shearPlus_g2, map_mul, h1, h2]
      calc
        q8Cyc * q8Cyc ^ 2 = q8Cyc ^ 3 := by group
        _ = 1 := q8Cyc_pow3)

/-- Target-conjugated and source-precomposed version of
`q8_e9_semidirect_iso_standard_of_first_gen`. -/
theorem q8_e9_semidirect_iso_standard_of_conj_first_gen
    (φ : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2)) (g : MulAut (QuaternionGroup 2))
    (σ : ElemAbelianRep 3 ≃* ElemAbelianRep 3)
    (h1 : ((MulAut.conj g).toMonoidHom.comp φ) (σ order72_E9_g1) = q8Cyc) :
    Nonempty (SemidirectProduct (QuaternionGroup 2) (ElemAbelianRep 3) φ ≃*
      order72_Q8_E9_cyc) := by
  let φ' : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2) := (MulAut.conj g).toMonoidHom.comp φ
  obtain ⟨e⟩ := q8_e9_semidirect_iso_standard_of_first_gen (φ'.comp σ.toMonoidHom) h1
  exact ⟨(semidirectProductCongrConj (φ := φ) g).trans
    ((semidirectProductCongrAut (φ := φ') σ).symm.trans e)⟩

/-- Every nontrivial `E9`-action on `Q8` gives the standard nontrivial semidirect-product
representative. -/
theorem q8_e9_semidirect_iso_standard_of_nontrivial
    (φ : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2)) (hφ : φ ≠ 1) :
    Nonempty (SemidirectProduct (QuaternionGroup 2) (ElemAbelianRep 3) φ ≃*
      order72_Q8_E9_cyc) := by
  obtain ⟨k, g, hg⟩ := q8_hom_nontrivial_conj_has_cyc_value card_order72_E9 φ hφ
  have hk : k ≠ 1 := by
    intro hk
    rw [hk, map_one] at hg
    exact q8Cyc_ne_one hg.symm
  obtain ⟨σ, hσ⟩ := order72_E9_exists_aut_map_g1 k hk
  exact q8_e9_semidirect_iso_standard_of_conj_first_gen φ g σ (by rwa [hσ])

/-- Actions of `E9` on `Q8` yield either the trivial semidirect product or the unique
nontrivial standard representative. -/
theorem q8_e9_semidirect_cases (φ : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2)) :
    Nonempty (SemidirectProduct (QuaternionGroup 2) (ElemAbelianRep 3) φ ≃*
      SemidirectProduct (QuaternionGroup 2) (ElemAbelianRep 3)
        (1 : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2))) ∨
    Nonempty (SemidirectProduct (QuaternionGroup 2) (ElemAbelianRep 3) φ ≃*
      order72_Q8_E9_cyc) := by
  by_cases hφ : φ = 1
  · exact Or.inl ⟨semidirectProductCongr_eq hφ⟩
  · exact Or.inr (q8_e9_semidirect_iso_standard_of_nontrivial φ hφ)

/-! ### `E8` order-`3` conjugacy classification: every nontrivial order-`3` automorphism of
`(ZMod 2)³` has a UNIQUE nontrivial fixed point.

Unlike `Q8` (only `8` order-`3` automorphisms, handled by hand), `E8` has `56`, too many to
case-split explicitly. Instead: `Fix(f) := {x | f x = x}` is a subgroup of `E8`, so
`Nat.card (Fix f) ∣ 8` (Lagrange). The cyclic group `⟨f⟩` (order `3`, since `f³=1 ∧ f≠1`) acts
on the `8`-element set `E8`, so `Nat.card E8 ≡ Nat.card (Fix f) [MOD 3]`
(`IsPGroup.card_modEq_card_fixedPoints`), i.e. `Nat.card (Fix f) ≡ 2 [MOD 3]`. Combined with
`Nat.card (Fix f) ∣ 8` and `f ≠ 1` (so `Nat.card (Fix f) ≠ 8`), the only divisor of `8` that is
`≡ 2 mod 3` and `≠ 8` is `2` — giving a UNIQUE nontrivial fixed point. -/

private def e8Fix (f : MulAut E8) : Subgroup E8 where
  carrier := {x | f x = x}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := map_one f
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

private theorem e8Fix_card_dvd (f : MulAut E8) : Nat.card (e8Fix f) ∣ 8 := by
  have h := Subgroup.card_subgroup_dvd_card (e8Fix f)
  have hE8 : Nat.card E8 = 8 := Nat.card_eq_fintype_card.trans (by decide)
  rwa [hE8] at h

private theorem e8_orderOf_three (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    orderOf f = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime hf3 hfne1

private def e8Gf (f : MulAut E8) : Subgroup (MulAut E8) := Subgroup.zpowers f

private theorem e8Gf_card (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    Nat.card (e8Gf f) = 3 := by
  rw [e8Gf, Nat.card_zpowers, e8_orderOf_three f hf3 hfne1]

private theorem e8Gf_isPGroup (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    IsPGroup 3 (e8Gf f) :=
  IsPGroup.of_card (n := 1) (by rw [e8Gf_card f hf3 hfne1, pow_one])

private theorem e8Gf_mem_iff (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1)
    (m : MulAut E8) : m ∈ e8Gf f ↔ m = 1 ∨ m = f ∨ m = f ^ 2 := by
  classical
  rw [e8Gf, mem_zpowers_iff_mem_range_orderOf, e8_orderOf_three f hf3 hfne1]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk3, rfl⟩
    interval_cases k
    · exact Or.inl (by rfl)
    · exact Or.inr (Or.inl (by rfl))
    · exact Or.inr (Or.inr (by rfl))
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, by rfl⟩
    · exact ⟨1, by norm_num, by rfl⟩
    · exact ⟨2, by norm_num, by rfl⟩

private theorem e8Fix_eq_fixedPoints (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    (MulAction.fixedPoints (e8Gf f) E8) = (e8Fix f : Set E8) := by
  ext x
  simp only [MulAction.fixedPoints, Set.mem_setOf_eq, e8Fix, Subgroup.coe_set_mk]
  constructor
  · intro h
    have hgen : (f : MulAut E8) ∈ e8Gf f := Subgroup.mem_zpowers f
    have := h ⟨f, hgen⟩
    rwa [MulAction.subgroup_smul_def, MulAut.smul_def] at this
  · intro hx m
    rw [MulAction.subgroup_smul_def, MulAut.smul_def]
    rcases (e8Gf_mem_iff f hf3 hfne1 m).mp m.2 with hm | hm | hm
    · change (m : MulAut E8) x = x
      rw [hm]; rfl
    · change (m : MulAut E8) x = x
      rw [hm]; exact hx
    · change (m : MulAut E8) x = x
      rw [hm, e8_pow_apply_eq_iterate]
      change f (f x) = x
      rw [hx, hx]

private theorem e8Fix_card_two (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    Nat.card (e8Fix f) = 2 := by
  have hcong : Nat.card E8 ≡ Nat.card (MulAction.fixedPoints (e8Gf f) E8) [MOD 3] :=
    (e8Gf_isPGroup f hf3 hfne1).card_modEq_card_fixedPoints E8
  rw [e8Fix_eq_fixedPoints f hf3 hfne1] at hcong
  have hE8card : Nat.card E8 = 8 := Nat.card_eq_fintype_card.trans (by decide)
  rw [hE8card] at hcong
  have hmod : Nat.card (e8Fix f) % 3 = 2 := by
    have h : (8 : ℕ) % 3 = Nat.card (e8Fix f) % 3 := hcong
    omega
  have hdvd := e8Fix_card_dvd f
  have hne8 : Nat.card (e8Fix f) ≠ 8 := by
    intro hc
    apply hfne1
    have htop : e8Fix f = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hc]
      exact (Nat.card_eq_fintype_card.trans (by decide) : Nat.card E8 = 8).symm
    apply DFunLike.ext
    intro x
    have hxmem : x ∈ e8Fix f := htop ▸ Subgroup.mem_top x
    exact hxmem
  have hle : Nat.card (e8Fix f) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card (e8Fix f) <;> omega

/-- A nontrivial order-`3` automorphism of `E8` fixes exactly one non-identity element. -/
theorem e8_order3_existsUnique_nontrivial_fixed (f : MulAut E8) (hf3 : f ^ 3 = 1)
    (hfne1 : f ≠ 1) : ∃! x : E8, x ≠ 1 ∧ f x = x := by
  let oneFix : e8Fix f := ⟨1, map_one f⟩
  obtain ⟨y, hyne, hyuniq⟩ :=
    (Nat.card_eq_two_iff' oneFix).1 (e8Fix_card_two f hf3 hfne1)
  refine ⟨y.1, ?_, ?_⟩
  · constructor
    · intro hy1
      apply hyne
      exact Subtype.ext hy1
    · exact y.2
  · intro z hz
    have hzFix : z ∈ e8Fix f := hz.2
    have hz_ne_oneFix : (⟨z, hzFix⟩ : e8Fix f) ≠ oneFix := by
      intro h
      exact hz.1 (congrArg Subtype.val h)
    exact congrArg Subtype.val (hyuniq ⟨z, hzFix⟩ hz_ne_oneFix)

/-- Once the unique non-identity fixed point `z` is chosen, the whole fixed-point set is
`{1, z}`. -/
theorem e8_order3_fixed_iff (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1)
    {z : E8} (hz : z ≠ 1 ∧ f z = z) (x : E8) : f x = x ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      obtain ⟨u, hu, huniq⟩ := e8_order3_existsUnique_nontrivial_fixed f hf3 hfne1
      exact (huniq x ⟨hx1, hx⟩).trans (huniq z hz).symm
  · rintro (rfl | rfl)
    · exact map_one f
    · exact hz.2

/-- The standard rotation `e8Rot` fixes exactly `1` and the first basis vector. -/
theorem e8Rot_fixed_iff (x : E8) :
    e8Rot x = x ↔ x = 1 ∨ x = (Multiplicative.ofAdd (1 : ZMod 2), 1, 1) := by
  rw [e8Rot_apply]
  revert x
  decide

/-- The first basis vector is the unique non-identity fixed point of `e8Rot`. -/
theorem e8Rot_unique_nontrivial_fixed :
    ∃! x : E8, x ≠ 1 ∧ e8Rot x = x :=
  e8_order3_existsUnique_nontrivial_fixed e8Rot e8Rot_pow3 e8Rot_ne_one

/-- Any non-identity vector of `E8` can be sent to the first basis vector by an automorphism.
This is the normalization step for the fixed line of a nontrivial order-`3` automorphism. -/
theorem e8_exists_aut_send_nontrivial_to_first (z : E8) (hz : z ≠ 1) :
    ∃ g : MulAut E8, g z = (Multiplicative.ofAdd (1 : ZMod 2), 1, 1) := by
  rcases e8gen z with h | h | h | h | h | h | h | h
  · exact absurd h hz
  · refine ⟨1, ?_⟩
    rw [h]
    decide
  · refine ⟨{
      toFun := fun ⟨p, q, r⟩ => (q, p, r)
      invFun := fun ⟨p, q, r⟩ => (q, p, r)
      left_inv := by decide
      right_inv := by decide
      map_mul' := by decide }, ?_⟩
    rw [h]
    decide
  · refine ⟨{
      toFun := fun ⟨p, q, r⟩ => (r, q, p)
      invFun := fun ⟨p, q, r⟩ => (r, q, p)
      left_inv := by decide
      right_inv := by decide
      map_mul' := by decide }, ?_⟩
    rw [h]
    decide
  · refine ⟨{
      toFun := fun ⟨p, q, r⟩ => (p, p * q, r)
      invFun := fun ⟨p, q, r⟩ => (p, p * q, r)
      left_inv := by decide
      right_inv := by decide
      map_mul' := by decide }, ?_⟩
    rw [h]
    decide
  · refine ⟨{
      toFun := fun ⟨p, q, r⟩ => (p, q, p * r)
      invFun := fun ⟨p, q, r⟩ => (p, q, p * r)
      left_inv := by decide
      right_inv := by decide
      map_mul' := by decide }, ?_⟩
    rw [h]
    decide
  · refine ⟨{
      toFun := fun ⟨p, q, r⟩ => (q, p, q * r)
      invFun := fun ⟨p, q, r⟩ => (q, p, p * r)
      left_inv := by decide
      right_inv := by decide
      map_mul' := by decide }, ?_⟩
    rw [h]
    decide
  · refine ⟨{
      toFun := fun ⟨p, q, r⟩ => (p, p * q, p * r)
      invFun := fun ⟨p, q, r⟩ => (p, p * q, p * r)
      left_inv := by decide
      right_inv := by decide
      map_mul' := by decide }, ?_⟩
    rw [h]
    decide

/-- Normalize the fixed line of a nontrivial order-`3` automorphism of `E8`: after conjugating,
the automorphism fixes the first basis vector. -/
theorem e8_order3_conj_fixes_first (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    ∃ h : MulAut E8, h ^ 3 = 1 ∧ h ≠ 1 ∧
      h (Multiplicative.ofAdd (1 : ZMod 2), 1, 1) =
        (Multiplicative.ofAdd (1 : ZMod 2), 1, 1) ∧
      ∃ g : MulAut E8, h = g * f * g⁻¹ := by
  obtain ⟨z, hz, -⟩ := e8_order3_existsUnique_nontrivial_fixed f hf3 hfne1
  obtain ⟨g, hg⟩ := e8_exists_aut_send_nontrivial_to_first z hz.1
  refine ⟨g * f * g⁻¹, ?_, ?_, ?_, ⟨g, rfl⟩⟩
  · calc
      (g * f * g⁻¹) ^ 3 = g * f ^ 3 * g⁻¹ := by
        rw [pow_three (g * f * g⁻¹), pow_three f]
        group
      _ = 1 := by rw [hf3]; group
  · intro htriv
    apply hfne1
    calc
      f = g⁻¹ * (g * f * g⁻¹) * g := by group
      _ = 1 := by rw [htriv]; group
  · change g (f (g⁻¹ (Multiplicative.ofAdd (1 : ZMod 2), 1, 1))) =
      (Multiplicative.ofAdd (1 : ZMod 2), 1, 1)
    rw [← hg]
    have hginv : g⁻¹ (g z) = z := by simp
    rw [hginv, hz.2, hg]

/-- A stronger normalization statement: after conjugating a nontrivial order-`3`
automorphism of `E8`, its fixed points are exactly `1` and the first basis vector. -/
theorem e8_order3_conj_fixed_line_first (f : MulAut E8) (hf3 : f ^ 3 = 1)
    (hfne1 : f ≠ 1) :
    ∃ h : MulAut E8, h ^ 3 = 1 ∧ h ≠ 1 ∧
      (∀ x : E8, h x = x ↔
        x = 1 ∨ x = (Multiplicative.ofAdd (1 : ZMod 2), 1, 1)) ∧
      ∃ g : MulAut E8, h = g * f * g⁻¹ := by
  obtain ⟨sigma, hsigma3, hsigma_ne1, hsigma_fix, g, hg⟩ :=
    e8_order3_conj_fixes_first f hf3 hfne1
  refine ⟨sigma, hsigma3, hsigma_ne1, ?_, g, hg⟩
  intro x
  exact e8_order3_fixed_iff sigma hsigma3 hsigma_ne1 ⟨by decide, hsigma_fix⟩ x

/-- Two automorphisms of `E8` are equal once they agree on the three standard generators. -/
theorem e8_mulAut_ext (f g : MulAut E8)
    (h1 : f e8g1 = g e8g1) (h2 : f e8g2 = g e8g2) (h3 : f e8g3 = g e8g3) :
    f = g := by
  apply DFunLike.ext
  intro x
  change f x = g x
  rcases e8gen x with hx | hx | hx | hx | hx | hx | hx | hx <;>
    simp [hx, map_mul, h1, h2, h3]

/-- The linear extension that fixes `e8g1` and sends `e8g2 ↦ A`, `e8g3 ↦ B`, written
as an explicit function on the eight elements of `E8`. -/
private def e8fixedExt (A B : E8) (x : E8) : E8 :=
  if x = 1 then 1
  else if x = e8g1 then e8g1
  else if x = e8g2 then A
  else if x = e8g3 then B
  else if x = e8g1 * e8g2 then e8g1 * A
  else if x = e8g1 * e8g3 then e8g1 * B
  else if x = e8g2 * e8g3 then A * B
  else e8g1 * A * B

@[simp] private theorem e8fixedExt_one (A B : E8) : e8fixedExt A B 1 = 1 := by
  simp [e8fixedExt]

@[simp] private theorem e8fixedExt_g1 (A B : E8) : e8fixedExt A B e8g1 = e8g1 := by
  rw [e8fixedExt]
  split
  · rename_i h
    exfalso
    revert h
    decide
  · simp

@[simp] private theorem e8fixedExt_g2 (A B : E8) : e8fixedExt A B e8g2 = A := by
  rw [e8fixedExt]
  split
  · rename_i h
    exfalso
    revert h
    decide
  · split
    · rename_i h
      exfalso
      revert h
      decide
    · simp

@[simp] private theorem e8fixedExt_g3 (A B : E8) : e8fixedExt A B e8g3 = B := by
  rw [e8fixedExt]
  split
  · rename_i h
    exfalso
    revert h
    decide
  · split
    · rename_i h
      exfalso
      revert h
      decide
    · split
      · rename_i h
        exfalso
        revert h
        decide
      · simp

@[simp] private theorem e8fixedExt_g1g2 (A B : E8) :
    e8fixedExt A B (e8g1 * e8g2) = e8g1 * A := by
  rw [e8fixedExt]
  repeat' first
    | split
      · rename_i h
        exfalso
        revert h
        decide
    | simp

@[simp] private theorem e8fixedExt_g1g3 (A B : E8) :
    e8fixedExt A B (e8g1 * e8g3) = e8g1 * B := by
  rw [e8fixedExt]
  repeat' first
    | split
      · rename_i h
        exfalso
        revert h
        decide
    | simp

@[simp] private theorem e8fixedExt_g2g3 (A B : E8) :
    e8fixedExt A B (e8g2 * e8g3) = A * B := by
  rw [e8fixedExt]
  repeat' first
    | split
      · rename_i h
        exfalso
        revert h
        decide
    | simp

@[simp] private theorem e8fixedExt_g1g2g3 (A B : E8) :
    e8fixedExt A B (e8g1 * e8g2 * e8g3) = e8g1 * A * B := by
  rw [e8fixedExt]
  repeat' first
    | split
      · rename_i h
        exfalso
        revert h
        decide
    | simp

private theorem e8_fixedExt_agrees (f : MulAut E8) (hf1 : f e8g1 = e8g1) (x : E8) :
    f x = e8fixedExt (f e8g2) (f e8g3) x := by
  rcases e8gen x with hx | hx | hx | hx | hx | hx | hx | hx <;>
    subst x <;> simp [map_mul, hf1]

/-- In the normalized fixed-line case, the order-`3` and fixed-point hypotheses for an
automorphism of `E8` reduce to the corresponding two-generator data of `e8fixedExt`. -/
theorem e8_order3_fixed_line_ext_data (f : MulAut E8) (hf3 : f ^ 3 = 1)
    (hfix : ∀ x : E8, f x = x ↔ x = 1 ∨ x = e8g1) :
    e8fixedExt (f e8g2) (f e8g3)
        (e8fixedExt (f e8g2) (f e8g3) (e8fixedExt (f e8g2) (f e8g3) e8g2)) = e8g2 ∧
      e8fixedExt (f e8g2) (f e8g3)
        (e8fixedExt (f e8g2) (f e8g3) (e8fixedExt (f e8g2) (f e8g3) e8g3)) = e8g3 ∧
      ∀ x : E8, e8fixedExt (f e8g2) (f e8g3) x = x ↔ x = 1 ∨ x = e8g1 := by
  have hf1 : f e8g1 = e8g1 := (hfix e8g1).mpr (Or.inr rfl)
  have hagree := e8_fixedExt_agrees f hf1
  refine ⟨?_, ?_, ?_⟩
  · have h : f (f (f e8g2)) = e8g2 := by
      have happ : (f ^ 3) e8g2 = e8g2 := by rw [hf3]; rfl
      exact happ
    rw [hagree e8g2, hagree (e8fixedExt (f e8g2) (f e8g3) e8g2),
      hagree (e8fixedExt (f e8g2) (f e8g3)
        (e8fixedExt (f e8g2) (f e8g3) e8g2))] at h
    exact h
  · have h : f (f (f e8g3)) = e8g3 := by
      have happ : (f ^ 3) e8g3 = e8g3 := by rw [hf3]; rfl
      exact happ
    rw [hagree e8g3, hagree (e8fixedExt (f e8g2) (f e8g3) e8g3),
      hagree (e8fixedExt (f e8g2) (f e8g3)
        (e8fixedExt (f e8g2) (f e8g3) e8g3))] at h
    exact h
  · intro x
    rw [← hagree x]
    exact hfix x

@[simp] theorem e8Rot_e8g1 : e8Rot e8g1 = e8g1 := by
  decide

@[simp] theorem e8Rot_e8g2 : e8Rot e8g2 = e8g3 := by
  decide

@[simp] theorem e8Rot_e8g3 : e8Rot e8g3 = e8g2 * e8g3 := by
  decide

@[simp] theorem e8Rot_sq_e8g1 : (e8Rot ^ 2) e8g1 = e8g1 := by
  decide

@[simp] theorem e8Rot_sq_e8g2 : (e8Rot ^ 2) e8g2 = e8g2 * e8g3 := by
  decide

@[simp] theorem e8Rot_sq_e8g3 : (e8Rot ^ 2) e8g3 = e8g2 := by
  decide

/-! The next three automorphisms fix `e8g1` and induce the identity on the quotient by
`⟨e8g1⟩`.  They are the elementary shears used to remove the four possible `e8g1`-twists in
the normalized fixed-line case. -/

def e8Shear2 : MulAut E8 where
  toFun := fun ⟨p, q, r⟩ => (p * q, q, r)
  invFun := fun ⟨p, q, r⟩ => (p * q, q, r)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

def e8Shear3 : MulAut E8 where
  toFun := fun ⟨p, q, r⟩ => (p * r, q, r)
  invFun := fun ⟨p, q, r⟩ => (p * r, q, r)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

def e8Shear23 : MulAut E8 where
  toFun := fun ⟨p, q, r⟩ => (p * q * r, q, r)
  invFun := fun ⟨p, q, r⟩ => (p * q * r, q, r)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

/-- The automorphism fixing `e8g1` and swapping `e8g2` with `e8g3`.  It conjugates
`e8Rot` to `e8Rot ^ 2`, so the two nontrivial rotations of the normalized quotient belong to
the same conjugacy class. -/
def e8Swap23 : MulAut E8 where
  toFun := fun ⟨p, q, r⟩ => (p, r, q)
  invFun := fun ⟨p, q, r⟩ => (p, r, q)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

theorem e8Shear2_inv : e8Shear2⁻¹ = e8Shear2 := by
  apply DFunLike.ext
  intro x
  change e8Shear2⁻¹ x = e8Shear2 x
  revert x
  decide

theorem e8Shear3_inv : e8Shear3⁻¹ = e8Shear3 := by
  apply DFunLike.ext
  intro x
  change e8Shear3⁻¹ x = e8Shear3 x
  revert x
  decide

theorem e8Shear23_inv : e8Shear23⁻¹ = e8Shear23 := by
  apply DFunLike.ext
  intro x
  change e8Shear23⁻¹ x = e8Shear23 x
  revert x
  decide

theorem e8Swap23_inv : e8Swap23⁻¹ = e8Swap23 := by
  apply DFunLike.ext
  intro x
  change e8Swap23⁻¹ x = e8Swap23 x
  revert x
  decide

@[simp] theorem e8Swap23_e8g1 : e8Swap23 e8g1 = e8g1 := by
  decide

@[simp] theorem e8Swap23_e8g2 : e8Swap23 e8g2 = e8g3 := by
  decide

@[simp] theorem e8Swap23_e8g3 : e8Swap23 e8g3 = e8g2 := by
  decide

@[simp] theorem e8Shear2_conj_rot_e8g1 :
    (e8Shear2 * e8Rot * e8Shear2⁻¹) e8g1 = e8g1 := by
  decide

@[simp] theorem e8Shear2_conj_rot_e8g2 :
    (e8Shear2 * e8Rot * e8Shear2⁻¹) e8g2 = e8g1 * e8g3 := by
  decide

@[simp] theorem e8Shear2_conj_rot_e8g3 :
    (e8Shear2 * e8Rot * e8Shear2⁻¹) e8g3 = e8g1 * e8g2 * e8g3 := by
  decide

@[simp] theorem e8Shear3_conj_rot_e8g1 :
    (e8Shear3 * e8Rot * e8Shear3⁻¹) e8g1 = e8g1 := by
  decide

@[simp] theorem e8Shear3_conj_rot_e8g2 :
    (e8Shear3 * e8Rot * e8Shear3⁻¹) e8g2 = e8g1 * e8g3 := by
  decide

@[simp] theorem e8Shear3_conj_rot_e8g3 :
    (e8Shear3 * e8Rot * e8Shear3⁻¹) e8g3 = e8g2 * e8g3 := by
  decide

@[simp] theorem e8Shear23_conj_rot_e8g1 :
    (e8Shear23 * e8Rot * e8Shear23⁻¹) e8g1 = e8g1 := by
  decide

@[simp] theorem e8Shear23_conj_rot_e8g2 :
    (e8Shear23 * e8Rot * e8Shear23⁻¹) e8g2 = e8g3 := by
  decide

@[simp] theorem e8Shear23_conj_rot_e8g3 :
    (e8Shear23 * e8Rot * e8Shear23⁻¹) e8g3 = e8g1 * e8g2 * e8g3 := by
  decide

@[simp] theorem e8Shear2_conj_rot_sq_e8g1 :
    (e8Shear2 * e8Rot ^ 2 * e8Shear2⁻¹) e8g1 = e8g1 := by
  decide

@[simp] theorem e8Shear2_conj_rot_sq_e8g2 :
    (e8Shear2 * e8Rot ^ 2 * e8Shear2⁻¹) e8g2 = e8g2 * e8g3 := by
  decide

@[simp] theorem e8Shear2_conj_rot_sq_e8g3 :
    (e8Shear2 * e8Rot ^ 2 * e8Shear2⁻¹) e8g3 = e8g1 * e8g2 := by
  decide

@[simp] theorem e8Shear3_conj_rot_sq_e8g1 :
    (e8Shear3 * e8Rot ^ 2 * e8Shear3⁻¹) e8g1 = e8g1 := by
  decide

@[simp] theorem e8Shear3_conj_rot_sq_e8g2 :
    (e8Shear3 * e8Rot ^ 2 * e8Shear3⁻¹) e8g2 = e8g1 * e8g2 * e8g3 := by
  decide

@[simp] theorem e8Shear3_conj_rot_sq_e8g3 :
    (e8Shear3 * e8Rot ^ 2 * e8Shear3⁻¹) e8g3 = e8g1 * e8g2 := by
  decide

@[simp] theorem e8Shear23_conj_rot_sq_e8g1 :
    (e8Shear23 * e8Rot ^ 2 * e8Shear23⁻¹) e8g1 = e8g1 := by
  decide

@[simp] theorem e8Shear23_conj_rot_sq_e8g2 :
    (e8Shear23 * e8Rot ^ 2 * e8Shear23⁻¹) e8g2 = e8g1 * e8g2 * e8g3 := by
  decide

@[simp] theorem e8Shear23_conj_rot_sq_e8g3 :
    (e8Shear23 * e8Rot ^ 2 * e8Shear23⁻¹) e8g3 = e8g2 := by
  decide

/-- Swapping the two quotient generators conjugates `e8Rot` to its square. -/
theorem e8Swap23_conj_rot : e8Swap23 * e8Rot * e8Swap23⁻¹ = e8Rot ^ 2 := by
  apply e8_mulAut_ext
  · decide
  · decide
  · decide

/-- Swapping the two quotient generators also conjugates `e8Rot ^ 2` back to `e8Rot`. -/
theorem e8Swap23_conj_rot_sq : e8Swap23 * e8Rot ^ 2 * e8Swap23⁻¹ = e8Rot := by
  apply e8_mulAut_ext
  · decide
  · decide
  · decide

theorem e8Rot_sq_is_conj_to_rot : ∃ g : MulAut E8, g * e8Rot ^ 2 * g⁻¹ = e8Rot :=
  ⟨e8Swap23, e8Swap23_conj_rot_sq⟩

/-- A wrapper useful after recognizing a normalized action as `e8Rot ^ 2`: it is still
conjugate to the standard representative `e8Rot`. -/
theorem e8_conj_to_rot_of_eq_rot_sq (f : MulAut E8) (hf : f = e8Rot ^ 2) :
    ∃ g : MulAut E8, g * f * g⁻¹ = e8Rot := by
  subst f
  exact e8Rot_sq_is_conj_to_rot

/-- Generator-value recognition for the standard rotation. -/
theorem e8_eq_rot_of_generators (f : MulAut E8) (h1 : f e8g1 = e8g1)
    (h2 : f e8g2 = e8g3) (h3 : f e8g3 = e8g2 * e8g3) : f = e8Rot := by
  exact e8_mulAut_ext f e8Rot h1 (by simpa using h2) (by simpa using h3)

/-- Generator-value recognition for the square of the standard rotation. -/
theorem e8_eq_rot_sq_of_generators (f : MulAut E8) (h1 : f e8g1 = e8g1)
    (h2 : f e8g2 = e8g2 * e8g3) (h3 : f e8g3 = e8g2) : f = e8Rot ^ 2 := by
  exact e8_mulAut_ext f (e8Rot ^ 2) h1 (by simpa using h2) (by simpa using h3)

/-- Once the normalized fixed-line analysis has reduced a nontrivial order-`3` automorphism
to one of the eight possible generator-value patterns, it is conjugate to the standard
rotation `e8Rot`.  The first four patterns are the four `e8g1`-twisted lifts of `e8Rot`; the
last four are the corresponding lifts of `e8Rot ^ 2`, which are conjugate back by
`e8Swap23`. -/
theorem e8_conj_to_rot_of_fixed_line_generator_cases (f : MulAut E8)
    (h1 : f e8g1 = e8g1)
    (hcases :
      (f e8g2 = e8g3 ∧ f e8g3 = e8g2 * e8g3) ∨
      (f e8g2 = e8g1 * e8g3 ∧ f e8g3 = e8g2 * e8g3) ∨
      (f e8g2 = e8g3 ∧ f e8g3 = e8g1 * e8g2 * e8g3) ∨
      (f e8g2 = e8g1 * e8g3 ∧ f e8g3 = e8g1 * e8g2 * e8g3) ∨
      (f e8g2 = e8g2 * e8g3 ∧ f e8g3 = e8g2) ∨
      (f e8g2 = e8g2 * e8g3 ∧ f e8g3 = e8g1 * e8g2) ∨
      (f e8g2 = e8g1 * e8g2 * e8g3 ∧ f e8g3 = e8g2) ∨
      (f e8g2 = e8g1 * e8g2 * e8g3 ∧ f e8g3 = e8g1 * e8g2)) :
    ∃ g : MulAut E8, g * f * g⁻¹ = e8Rot := by
  rcases hcases with h | h | h | h | h | h | h | h
  · have hf : f = e8Rot := e8_eq_rot_of_generators f h1 h.1 h.2
    subst f
    exact ⟨1, by simp⟩
  · have hf : f = e8Shear3 * e8Rot * e8Shear3⁻¹ := by
      exact e8_mulAut_ext f (e8Shear3 * e8Rot * e8Shear3⁻¹) h1
        (by rw [e8Shear3_conj_rot_e8g2]; exact h.1)
        (by rw [e8Shear3_conj_rot_e8g3]; exact h.2)
    refine ⟨e8Shear3⁻¹, ?_⟩
    rw [hf]
    group
  · have hf : f = e8Shear23 * e8Rot * e8Shear23⁻¹ := by
      exact e8_mulAut_ext f (e8Shear23 * e8Rot * e8Shear23⁻¹) h1
        (by rw [e8Shear23_conj_rot_e8g2]; exact h.1)
        (by rw [e8Shear23_conj_rot_e8g3]; exact h.2)
    refine ⟨e8Shear23⁻¹, ?_⟩
    rw [hf]
    group
  · have hf : f = e8Shear2 * e8Rot * e8Shear2⁻¹ := by
      exact e8_mulAut_ext f (e8Shear2 * e8Rot * e8Shear2⁻¹) h1
        (by rw [e8Shear2_conj_rot_e8g2]; exact h.1)
        (by rw [e8Shear2_conj_rot_e8g3]; exact h.2)
    refine ⟨e8Shear2⁻¹, ?_⟩
    rw [hf]
    group
  · have hf : f = e8Rot ^ 2 := e8_eq_rot_sq_of_generators f h1 h.1 h.2
    exact e8_conj_to_rot_of_eq_rot_sq f hf
  · have hf : f = e8Shear2 * e8Rot ^ 2 * e8Shear2⁻¹ := by
      exact e8_mulAut_ext f (e8Shear2 * e8Rot ^ 2 * e8Shear2⁻¹) h1
        (by rw [e8Shear2_conj_rot_sq_e8g2]; exact h.1)
        (by rw [e8Shear2_conj_rot_sq_e8g3]; exact h.2)
    refine ⟨e8Swap23 * e8Shear2⁻¹, ?_⟩
    rw [hf]
    calc
      (e8Swap23 * e8Shear2⁻¹) * (e8Shear2 * e8Rot ^ 2 * e8Shear2⁻¹) *
          (e8Swap23 * e8Shear2⁻¹)⁻¹ = e8Swap23 * e8Rot ^ 2 * e8Swap23⁻¹ := by group
      _ = e8Rot := e8Swap23_conj_rot_sq
  · have hf : f = e8Shear23 * e8Rot ^ 2 * e8Shear23⁻¹ := by
      exact e8_mulAut_ext f (e8Shear23 * e8Rot ^ 2 * e8Shear23⁻¹) h1
        (by rw [e8Shear23_conj_rot_sq_e8g2]; exact h.1)
        (by rw [e8Shear23_conj_rot_sq_e8g3]; exact h.2)
    refine ⟨e8Swap23 * e8Shear23⁻¹, ?_⟩
    rw [hf]
    calc
      (e8Swap23 * e8Shear23⁻¹) * (e8Shear23 * e8Rot ^ 2 * e8Shear23⁻¹) *
          (e8Swap23 * e8Shear23⁻¹)⁻¹ = e8Swap23 * e8Rot ^ 2 * e8Swap23⁻¹ := by group
      _ = e8Rot := e8Swap23_conj_rot_sq
  · have hf : f = e8Shear3 * e8Rot ^ 2 * e8Shear3⁻¹ := by
      exact e8_mulAut_ext f (e8Shear3 * e8Rot ^ 2 * e8Shear3⁻¹) h1
        (by rw [e8Shear3_conj_rot_sq_e8g2]; exact h.1)
        (by rw [e8Shear3_conj_rot_sq_e8g3]; exact h.2)
    refine ⟨e8Swap23 * e8Shear3⁻¹, ?_⟩
    rw [hf]
    calc
      (e8Swap23 * e8Shear3⁻¹) * (e8Shear3 * e8Rot ^ 2 * e8Shear3⁻¹) *
          (e8Swap23 * e8Shear3⁻¹)⁻¹ = e8Swap23 * e8Rot ^ 2 * e8Swap23⁻¹ := by group
      _ = e8Rot := e8Swap23_conj_rot_sq

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The finite core of the normalized fixed-line classification: if a putative extension
fixes exactly `{1, e8g1}` and has cube equal to the identity on the two remaining generators,
then its generator values are one of the eight lift patterns handled by
`e8_conj_to_rot_of_fixed_line_generator_cases`. -/
theorem e8_fixedExt_generator_cases (A B : E8)
    (h3₂ : e8fixedExt A B (e8fixedExt A B (e8fixedExt A B e8g2)) = e8g2)
    (h3₃ : e8fixedExt A B (e8fixedExt A B (e8fixedExt A B e8g3)) = e8g3)
    (hfix : ∀ x : E8, e8fixedExt A B x = x ↔ x = 1 ∨ x = e8g1) :
    (A = e8g3 ∧ B = e8g2 * e8g3) ∨
    (A = e8g1 * e8g3 ∧ B = e8g2 * e8g3) ∨
    (A = e8g3 ∧ B = e8g1 * e8g2 * e8g3) ∨
    (A = e8g1 * e8g3 ∧ B = e8g1 * e8g2 * e8g3) ∨
    (A = e8g2 * e8g3 ∧ B = e8g2) ∨
    (A = e8g2 * e8g3 ∧ B = e8g1 * e8g2) ∨
    (A = e8g1 * e8g2 * e8g3 ∧ B = e8g2) ∨
    (A = e8g1 * e8g2 * e8g3 ∧ B = e8g1 * e8g2) := by
  rcases e8gen A with hA | hA | hA | hA | hA | hA | hA | hA <;>
  rcases e8gen B with hB | hB | hB | hB | hB | hB | hB | hB <;>
    subst A <;> subst B <;>
    first
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))
      | exfalso
        first
          | exact (show ¬ _ from by decide) h3₂
          | exact (show ¬ _ from by decide) h3₃
          | exact (show ¬ _ from by decide) ((hfix e8g2).mp (by simp))
          | exact (show ¬ _ from by decide) ((hfix e8g3).mp (by simp))
          | exact (show ¬ _ from by decide) ((hfix (e8g1 * e8g2)).mp (by simp))
          | exact (show ¬ _ from by decide) ((hfix (e8g1 * e8g3)).mp (by simp))
          | exact (show ¬ _ from by decide) ((hfix (e8g2 * e8g3)).mp (by simp))
          | exact (show ¬ _ from by decide) ((hfix (e8g1 * e8g2 * e8g3)).mp (by simp))

/-- A normalized nontrivial order-`3` automorphism of `E8` whose fixed line is
`{1, e8g1}` is conjugate to the standard rotation `e8Rot`. -/
theorem e8_order3_fixed_line_conj_to_rot (f : MulAut E8) (hf3 : f ^ 3 = 1)
    (hfix : ∀ x : E8, f x = x ↔ x = 1 ∨ x = e8g1) :
    ∃ g : MulAut E8, g * f * g⁻¹ = e8Rot := by
  have hf1 : f e8g1 = e8g1 := (hfix e8g1).mpr (Or.inr rfl)
  rcases e8_order3_fixed_line_ext_data f hf3 hfix with ⟨h3₂, h3₃, hfixExt⟩
  have hcases := e8_fixedExt_generator_cases (f e8g2) (f e8g3) h3₂ h3₃ hfixExt
  exact e8_conj_to_rot_of_fixed_line_generator_cases f hf1 hcases

/-- Every nontrivial order-`3` automorphism of `E8` is conjugate to the standard rotation. -/
theorem e8_order3_conj_to_rot (f : MulAut E8) (hf3 : f ^ 3 = 1) (hfne1 : f ≠ 1) :
    ∃ g : MulAut E8, g * f * g⁻¹ = e8Rot := by
  obtain ⟨h, hh3, _hhne, hfix, g0, hg0⟩ := e8_order3_conj_fixed_line_first f hf3 hfne1
  obtain ⟨g1, hg1⟩ := e8_order3_fixed_line_conj_to_rot h hh3 hfix
  refine ⟨g1 * g0, ?_⟩
  calc
    (g1 * g0) * f * (g1 * g0)⁻¹ = g1 * (g0 * f * g0⁻¹) * g1⁻¹ := by group
    _ = g1 * h * g1⁻¹ := by rw [← hg0]
    _ = e8Rot := hg1

/-- The order-`3` part of the centralizer of `e8Rot` in `Aut(E8)` is the cyclic subgroup
generated by `e8Rot`. -/
theorem e8_commute_rot_order3_cases (f : MulAut E8) (hf3 : f ^ 3 = 1)
    (hcomm : f * e8Rot = e8Rot * f) : f = 1 ∨ f = e8Rot ∨ f = e8Rot ^ 2 := by
  by_cases hf1 : f = 1
  · exact Or.inl hf1
  · right
    obtain ⟨z, hz, huniq⟩ := e8_order3_existsUnique_nontrivial_fixed f hf3 hf1
    have hcomm_apply : ∀ x : E8, f (e8Rot x) = e8Rot (f x) := by
      intro x
      have hx := congrArg (fun u : MulAut E8 => u x) hcomm
      change f (e8Rot x) = e8Rot (f x) at hx
      exact hx
    have hzrot : f (e8Rot z) = e8Rot z := by rw [hcomm_apply z, hz.2]
    have hzrot_ne : e8Rot z ≠ 1 := by
      intro h
      exact hz.1 (e8Rot.injective (by rw [h, map_one]))
    have hrotfix : e8Rot z = z := huniq (e8Rot z) ⟨hzrot_ne, hzrot⟩
    have hz_eq_g1 : z = e8g1 := by
      rcases (e8Rot_fixed_iff z).mp hrotfix with hz1 | hzg1
      · exact (False.elim (hz.1 hz1))
      · exact hzg1
    have hf_g1 : f e8g1 = e8g1 := by rw [← hz_eq_g1]; exact hz.2
    have hfix : ∀ x : E8, f x = x ↔ x = 1 ∨ x = e8g1 :=
      e8_order3_fixed_iff f hf3 hf1 ⟨by decide, hf_g1⟩
    rcases e8_order3_fixed_line_ext_data f hf3 hfix with ⟨h3₂, h3₃, hfixExt⟩
    have hcases := e8_fixedExt_generator_cases (f e8g2) (f e8g3) h3₂ h3₃ hfixExt
    have hcomm_ext : ∀ x : E8, e8fixedExt (f e8g2) (f e8g3) (e8Rot x) =
        e8Rot (e8fixedExt (f e8g2) (f e8g3) x) := by
      intro x
      rw [← e8_fixedExt_agrees f hf_g1 (e8Rot x), ← e8_fixedExt_agrees f hf_g1 x]
      exact hcomm_apply x
    rcases hcases with h | h | h | h | h | h | h | h
    · left
      exact e8_eq_rot_of_generators f hf_g1 h.1 h.2
    · exfalso
      have hc := hcomm_ext
      rw [h.1, h.2] at hc
      exact (show ¬ _ from by decide) hc
    · exfalso
      have hc := hcomm_ext
      rw [h.1, h.2] at hc
      exact (show ¬ _ from by decide) hc
    · exfalso
      have hc := hcomm_ext
      rw [h.1, h.2] at hc
      exact (show ¬ _ from by decide) hc
    · right
      exact e8_eq_rot_sq_of_generators f hf_g1 h.1 h.2
    · exfalso
      have hc := hcomm_ext
      rw [h.1, h.2] at hc
      exact (show ¬ _ from by decide) hc
    · exfalso
      have hc := hcomm_ext
      rw [h.1, h.2] at hc
      exact (show ¬ _ from by decide) hc
    · exfalso
      have hc := hcomm_ext
      rw [h.1, h.2] at hc
      exact (show ¬ _ from by decide) hc

/-- A nontrivial action of a group of order `9` on `E8` contains an element whose image is
`Aut(E8)`-conjugate to the standard `e8Rot`. -/
theorem e8_hom_nontrivial_elem_conj_to_rot {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 9) (φ : K →* MulAut E8) (hφ : φ ≠ 1) :
    ∃ k : K, φ k ≠ 1 ∧ ∃ g : MulAut E8, g * φ k * g⁻¹ = e8Rot := by
  have hnontriv : ∃ k : K, φ k ≠ 1 := exists_apply_ne_one_of_monoidHom_ne_one φ hφ
  obtain ⟨k, hkne⟩ := hnontriv
  have hk9 : k ^ 9 = 1 := by
    exact orderOf_dvd_iff_pow_eq_one.mp (hK ▸ orderOf_dvd_natCard k)
  have hφ9 : (φ k) ^ 9 = 1 := by
    rw [← map_pow, hk9, map_one]
  have hφ3 : (φ k) ^ 3 = 1 := e8_pow9_imp_pow3 (φ k) hφ9
  exact ⟨k, hkne, e8_order3_conj_to_rot (φ k) hφ3 hkne⟩

/-- Every value of an action of a group of order `9` on `E8` has cube equal to the identity. -/
theorem e8_hom_apply_pow3_of_card9 {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 9) (φ : K →* MulAut E8) (k : K) :
    (φ k) ^ 3 = 1 := by
  have hk9 : k ^ 9 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hK ▸ orderOf_dvd_natCard k)
  have hφ9 : (φ k) ^ 9 = 1 := by
    rw [← map_pow, hk9, map_one]
  exact e8_pow9_imp_pow3 (φ k) hφ9

/-- Pointwise form for order-`9` actions on `E8`: each element acts trivially or by an
automorphism conjugate to `e8Rot`. -/
theorem e8_hom_apply_eq_one_or_conj_to_rot {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 9) (φ : K →* MulAut E8) (k : K) :
    φ k = 1 ∨ ∃ g : MulAut E8, g * φ k * g⁻¹ = e8Rot := by
  by_cases hk : φ k = 1
  · exact Or.inl hk
  · exact Or.inr (e8_order3_conj_to_rot (φ k) (e8_hom_apply_pow3_of_card9 hK φ k) hk)

/-- Orbit-move form of `e8_hom_nontrivial_elem_conj_to_rot`: after conjugating the whole
action by an automorphism of `E8`, some element of the order-`9` source acts exactly as
`e8Rot`. -/
theorem e8_hom_nontrivial_conj_has_rot_value {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 9) (φ : K →* MulAut E8) (hφ : φ ≠ 1) :
    ∃ k : K, ∃ g : MulAut E8, ((MulAut.conj g).toMonoidHom.comp φ) k = e8Rot := by
  obtain ⟨k, _hkne, g, hg⟩ := e8_hom_nontrivial_elem_conj_to_rot hK φ hφ
  exact ⟨k, g, by simpa [MonoidHom.comp_apply, MulAut.conj_apply] using hg⟩

/-- Every nontrivial `C9`-action on `E8` is target-conjugate to the standard action. -/
theorem e8_c9_action_conj_eq_standard (φ : CyclicRep 9 →* MulAut E8) (hφ : φ ≠ 1) :
    ∃ g : MulAut E8, (MulAut.conj g).toMonoidHom.comp φ = e8RotActionC9 := by
  let c : CyclicRep 9 := Multiplicative.ofAdd (1 : ZMod 9)
  have hcne : φ c ≠ 1 := by
    intro hc
    apply hφ
    apply cyclicRep_hom_ext
    simp [c, hc]
  have hc3 : (φ c) ^ 3 = 1 := e8_hom_apply_pow3_of_card9 card_order72_C9 φ c
  obtain ⟨g, hg⟩ := e8_order3_conj_to_rot (φ c) hc3 hcne
  refine ⟨g, cyclicRep_hom_ext ?_⟩
  change (MulAut.conj g) (φ c) = e8RotActionC9 c
  simpa [c, MonoidHom.comp_apply, MulAut.conj_apply] using hg

/-- Semidirect-product form of `e8_c9_action_conj_eq_standard`. -/
theorem e8_c9_semidirect_iso_standard (φ : CyclicRep 9 →* MulAut E8) (hφ : φ ≠ 1) :
    Nonempty (SemidirectProduct E8 (CyclicRep 9) φ ≃* order72_E8_C9_rot) := by
  obtain ⟨g, hg⟩ := e8_c9_action_conj_eq_standard φ hφ
  exact ⟨(semidirectProductCongrConj (φ := φ) g).trans (semidirectProductCongr_eq hg)⟩

/-- Actions of `C9` on `E8` yield either the trivial semidirect product or the unique
nontrivial standard representative. -/
theorem e8_c9_semidirect_cases (φ : CyclicRep 9 →* MulAut E8) :
    Nonempty (SemidirectProduct E8 (CyclicRep 9) φ ≃*
      SemidirectProduct E8 (CyclicRep 9) (1 : CyclicRep 9 →* MulAut E8)) ∨
    Nonempty (SemidirectProduct E8 (CyclicRep 9) φ ≃* order72_E8_C9_rot) := by
  by_cases hφ : φ = 1
  · exact Or.inl ⟨semidirectProductCongr_eq hφ⟩
  · exact Or.inr (e8_c9_semidirect_iso_standard φ hφ)

/-- An `E9`-action on `E8` with the standard values on the two generators is the standard
action. -/
theorem e8_e9_action_eq_standard_of_gen_values (φ : ElemAbelianRep 3 →* MulAut E8)
    (h1 : φ order72_E9_g1 = e8Rot) (h2 : φ order72_E9_g2 = 1) :
    φ = e8RotActionE9 := by
  apply elemAbelianRep3_hom_ext
  · simpa [order72_E9_g1] using h1
  · simpa [order72_E9_g2] using h2

/-- Source-normalized form for the standard nontrivial `E9`-action on `E8`. -/
theorem e8_e9_action_precomp_eq_standard (φ : ElemAbelianRep 3 →* MulAut E8)
    (σ : ElemAbelianRep 3 ≃* ElemAbelianRep 3)
    (h1 : φ (σ order72_E9_g1) = e8Rot) (h2 : φ (σ order72_E9_g2) = 1) :
    φ.comp σ.toMonoidHom = e8RotActionE9 :=
  e8_e9_action_eq_standard_of_gen_values (φ.comp σ.toMonoidHom) h1 h2

/-- If an `E9`-action on `E8` becomes standard after target conjugation and a source
automorphism, then its semidirect product is the standard `E8 ⋊ E9` representative. -/
theorem e8_e9_semidirect_iso_standard_of_conj_precomp
    (φ : ElemAbelianRep 3 →* MulAut E8) (g : MulAut E8)
    (σ : ElemAbelianRep 3 ≃* ElemAbelianRep 3)
    (h1 : ((MulAut.conj g).toMonoidHom.comp φ) (σ order72_E9_g1) = e8Rot)
    (h2 : ((MulAut.conj g).toMonoidHom.comp φ) (σ order72_E9_g2) = 1) :
    Nonempty (SemidirectProduct E8 (ElemAbelianRep 3) φ ≃* order72_E8_E9_rot) := by
  let φ' : ElemAbelianRep 3 →* MulAut E8 := (MulAut.conj g).toMonoidHom.comp φ
  have hstd : φ'.comp σ.toMonoidHom = e8RotActionE9 :=
    e8_e9_action_precomp_eq_standard φ' σ h1 h2
  exact ⟨(semidirectProductCongrConj (φ := φ) g).trans
    ((semidirectProductCongrAut (φ := φ') σ).symm.trans (semidirectProductCongr_eq hstd))⟩

/-- If the first generator of `E9` acts by `e8Rot`, then the whole `E9`-action on `E8`
is equivalent to the standard representative.  The second generator is forced into the
cyclic centralizer of `e8Rot`, and a source shear removes it. -/
theorem e8_e9_semidirect_iso_standard_of_first_gen (φ : ElemAbelianRep 3 →* MulAut E8)
    (h1 : φ order72_E9_g1 = e8Rot) :
    Nonempty (SemidirectProduct E8 (ElemAbelianRep 3) φ ≃* order72_E8_E9_rot) := by
  have hcomm : φ order72_E9_g2 * e8Rot = e8Rot * φ order72_E9_g2 := by
    have hsrc : order72_E9_g2 * order72_E9_g1 = order72_E9_g1 * order72_E9_g2 := by
      ext <;> simp [order72_E9_g1, order72_E9_g2, mul_comm]
    calc
      φ order72_E9_g2 * e8Rot = φ order72_E9_g2 * φ order72_E9_g1 := by rw [h1]
      _ = φ (order72_E9_g2 * order72_E9_g1) := by rw [map_mul]
      _ = φ (order72_E9_g1 * order72_E9_g2) := by rw [hsrc]
      _ = φ order72_E9_g1 * φ order72_E9_g2 := by rw [map_mul]
      _ = e8Rot * φ order72_E9_g2 := by rw [h1]
  have hpow : (φ order72_E9_g2) ^ 3 = 1 :=
    e8_hom_apply_pow3_of_card9 card_order72_E9 φ order72_E9_g2
  rcases e8_commute_rot_order3_cases (φ order72_E9_g2) hpow hcomm with h2 | h2 | h2
  · exact e8_e9_semidirect_iso_standard_of_conj_precomp φ 1 (MulEquiv.refl _) (by
      simpa [MonoidHom.comp_apply, MulAut.conj_apply] using h1) (by
      simpa [MonoidHom.comp_apply, MulAut.conj_apply] using h2)
  · exact e8_e9_semidirect_iso_standard_of_conj_precomp φ 1 order72_E9_shearPlus.symm (by
      simpa [MonoidHom.comp_apply, MulAut.conj_apply, order72_E9_shearMinus_g1] using h1) (by
      change φ (order72_E9_shearPlus.symm order72_E9_g2) = 1
      rw [order72_E9_shearMinus_g2, map_mul, map_pow, h1, h2]
      calc
        e8Rot ^ 2 * e8Rot = e8Rot ^ 3 := by group
        _ = 1 := e8Rot_pow3)
  · exact e8_e9_semidirect_iso_standard_of_conj_precomp φ 1 order72_E9_shearPlus (by
      simpa [MonoidHom.comp_apply, MulAut.conj_apply, order72_E9_shearPlus_g1] using h1) (by
      change φ (order72_E9_shearPlus order72_E9_g2) = 1
      rw [order72_E9_shearPlus_g2, map_mul, h1, h2]
      calc
        e8Rot * e8Rot ^ 2 = e8Rot ^ 3 := by group
        _ = 1 := e8Rot_pow3)

/-- Target-conjugated and source-precomposed version of
`e8_e9_semidirect_iso_standard_of_first_gen`. -/
theorem e8_e9_semidirect_iso_standard_of_conj_first_gen
    (φ : ElemAbelianRep 3 →* MulAut E8) (g : MulAut E8)
    (σ : ElemAbelianRep 3 ≃* ElemAbelianRep 3)
    (h1 : ((MulAut.conj g).toMonoidHom.comp φ) (σ order72_E9_g1) = e8Rot) :
    Nonempty (SemidirectProduct E8 (ElemAbelianRep 3) φ ≃* order72_E8_E9_rot) := by
  let φ' : ElemAbelianRep 3 →* MulAut E8 := (MulAut.conj g).toMonoidHom.comp φ
  obtain ⟨e⟩ := e8_e9_semidirect_iso_standard_of_first_gen (φ'.comp σ.toMonoidHom) h1
  exact ⟨(semidirectProductCongrConj (φ := φ) g).trans
    ((semidirectProductCongrAut (φ := φ') σ).symm.trans e)⟩

/-- Every nontrivial `E9`-action on `E8` gives the standard nontrivial semidirect-product
representative. -/
theorem e8_e9_semidirect_iso_standard_of_nontrivial
    (φ : ElemAbelianRep 3 →* MulAut E8) (hφ : φ ≠ 1) :
    Nonempty (SemidirectProduct E8 (ElemAbelianRep 3) φ ≃* order72_E8_E9_rot) := by
  obtain ⟨k, g, hg⟩ := e8_hom_nontrivial_conj_has_rot_value card_order72_E9 φ hφ
  have hk : k ≠ 1 := by
    intro hk
    rw [hk, map_one] at hg
    exact e8Rot_ne_one hg.symm
  obtain ⟨σ, hσ⟩ := order72_E9_exists_aut_map_g1 k hk
  exact e8_e9_semidirect_iso_standard_of_conj_first_gen φ g σ (by rwa [hσ])

/-- Actions of `E9` on `E8` yield either the trivial semidirect product or the unique
nontrivial standard representative. -/
theorem e8_e9_semidirect_cases (φ : ElemAbelianRep 3 →* MulAut E8) :
    Nonempty (SemidirectProduct E8 (ElemAbelianRep 3) φ ≃*
      SemidirectProduct E8 (ElemAbelianRep 3) (1 : ElemAbelianRep 3 →* MulAut E8)) ∨
    Nonempty (SemidirectProduct E8 (ElemAbelianRep 3) φ ≃* order72_E8_E9_rot) := by
  by_cases hφ : φ = 1
  · exact Or.inl ⟨semidirectProductCongr_eq hφ⟩
  · exact Or.inr (e8_e9_semidirect_iso_standard_of_nontrivial φ hφ)

/-! ### Exhaustion of the Sylow-`2`-normal branch. -/

/-- The representatives reached by the Sylow-`2`-normal branch: all direct products
`H × K` with `|H| = 8`, `|K| = 9`, plus the four nontrivial `Q8`/`E8` actions. -/
abbrev order72Sylow2NormalRepCases (G : Type*) [Group G] : Prop :=
  Nonempty (G ≃* Multiplicative (ZMod 8) × CyclicRep 9) ∨
    Nonempty (G ≃* Multiplicative (ZMod 8) × ElemAbelianRep 3) ∨
    Nonempty (G ≃* H2 × CyclicRep 9) ∨
    Nonempty (G ≃* H2 × ElemAbelianRep 3) ∨
    Nonempty (G ≃* E8 × CyclicRep 9) ∨
    Nonempty (G ≃* E8 × ElemAbelianRep 3) ∨
    Nonempty (G ≃* DihedralGroup 4 × CyclicRep 9) ∨
    Nonempty (G ≃* DihedralGroup 4 × ElemAbelianRep 3) ∨
    Nonempty (G ≃* QuaternionGroup 2 × CyclicRep 9) ∨
    Nonempty (G ≃* QuaternionGroup 2 × ElemAbelianRep 3) ∨
    Nonempty (G ≃* order72_Q8_C9_cyc) ∨
    Nonempty (G ≃* order72_Q8_E9_cyc) ∨
    Nonempty (G ≃* order72_E8_C9_rot) ∨
    Nonempty (G ≃* order72_E8_E9_rot)

private theorem order72RepCases_c8_c9 {G : Type*} [Group G]
    (h : Nonempty (G ≃* Multiplicative (ZMod 8) × CyclicRep 9)) :
    order72Sylow2NormalRepCases G :=
  Or.inl h

private theorem order72RepCases_c8_e9 {G : Type*} [Group G]
    (h : Nonempty (G ≃* Multiplicative (ZMod 8) × ElemAbelianRep 3)) :
    order72Sylow2NormalRepCases G := by
  right
  left
  exact h

private theorem order72RepCases_h2_c9 {G : Type*} [Group G]
    (h : Nonempty (G ≃* H2 × CyclicRep 9)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  left
  exact h

private theorem order72RepCases_h2_e9 {G : Type*} [Group G]
    (h : Nonempty (G ≃* H2 × ElemAbelianRep 3)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  right
  left
  exact h

private theorem order72RepCases_e8_c9_prod {G : Type*} [Group G]
    (h : Nonempty (G ≃* E8 × CyclicRep 9)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  right
  right
  left
  exact h

private theorem order72RepCases_e8_e9_prod {G : Type*} [Group G]
    (h : Nonempty (G ≃* E8 × ElemAbelianRep 3)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72RepCases_d4_c9 {G : Type*} [Group G]
    (h : Nonempty (G ≃* DihedralGroup 4 × CyclicRep 9)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72RepCases_d4_e9 {G : Type*} [Group G]
    (h : Nonempty (G ≃* DihedralGroup 4 × ElemAbelianRep 3)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72RepCases_q8_c9_prod {G : Type*} [Group G]
    (h : Nonempty (G ≃* QuaternionGroup 2 × CyclicRep 9)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72RepCases_q8_e9_prod {G : Type*} [Group G]
    (h : Nonempty (G ≃* QuaternionGroup 2 × ElemAbelianRep 3)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72RepCases_q8_c9 {G : Type*} [Group G]
    (h : Nonempty (G ≃* order72_Q8_C9_cyc)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72RepCases_q8_e9 {G : Type*} [Group G]
    (h : Nonempty (G ≃* order72_Q8_E9_cyc)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72RepCases_e8_c9 {G : Type*} [Group G]
    (h : Nonempty (G ≃* order72_E8_C9_rot)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72RepCases_e8_e9 {G : Type*} [Group G]
    (h : Nonempty (G ≃* order72_E8_E9_rot)) :
    order72Sylow2NormalRepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  exact h

private theorem order72_classification_of_c8_c9_action {G : Type*} [Group G]
    {φ : CyclicRep 9 →* MulAut (Multiplicative (ZMod 8))}
    (e : G ≃* SemidirectProduct (Multiplicative (ZMod 8)) (CyclicRep 9) φ) :
    order72Sylow2NormalRepCases G := by
  obtain ⟨eh⟩ := c8_order9_semidirect_iso_prod card_order72_C9 φ
  exact order72RepCases_c8_c9 ⟨e.trans eh⟩

private theorem order72_classification_of_c8_e9_action {G : Type*} [Group G]
    {φ : ElemAbelianRep 3 →* MulAut (Multiplicative (ZMod 8))}
    (e : G ≃* SemidirectProduct (Multiplicative (ZMod 8)) (ElemAbelianRep 3) φ) :
    order72Sylow2NormalRepCases G := by
  obtain ⟨eh⟩ := c8_order9_semidirect_iso_prod card_order72_E9 φ
  exact order72RepCases_c8_e9 ⟨e.trans eh⟩

private theorem order72_classification_of_h2_c9_action {G : Type*} [Group G]
    {φ : CyclicRep 9 →* MulAut H2} (e : G ≃* SemidirectProduct H2 (CyclicRep 9) φ) :
    order72Sylow2NormalRepCases G := by
  obtain ⟨eh⟩ := h2_order9_semidirect_iso_prod card_order72_C9 φ
  exact order72RepCases_h2_c9 ⟨e.trans eh⟩

private theorem order72_classification_of_h2_e9_action {G : Type*} [Group G]
    {φ : ElemAbelianRep 3 →* MulAut H2}
    (e : G ≃* SemidirectProduct H2 (ElemAbelianRep 3) φ) :
    order72Sylow2NormalRepCases G := by
  obtain ⟨eh⟩ := h2_order9_semidirect_iso_prod card_order72_E9 φ
  exact order72RepCases_h2_e9 ⟨e.trans eh⟩

private theorem order72_classification_of_d4_c9_action {G : Type*} [Group G]
    {φ : CyclicRep 9 →* MulAut (DihedralGroup 4)}
    (e : G ≃* SemidirectProduct (DihedralGroup 4) (CyclicRep 9) φ) :
    order72Sylow2NormalRepCases G := by
  obtain ⟨eh⟩ := d4_order9_semidirect_iso_prod card_order72_C9 φ
  exact order72RepCases_d4_c9 ⟨e.trans eh⟩

private theorem order72_classification_of_d4_e9_action {G : Type*} [Group G]
    {φ : ElemAbelianRep 3 →* MulAut (DihedralGroup 4)}
    (e : G ≃* SemidirectProduct (DihedralGroup 4) (ElemAbelianRep 3) φ) :
    order72Sylow2NormalRepCases G := by
  obtain ⟨eh⟩ := d4_order9_semidirect_iso_prod card_order72_E9 φ
  exact order72RepCases_d4_e9 ⟨e.trans eh⟩

private theorem order72_classification_of_q8_c9_action {G : Type*} [Group G]
    {φ : CyclicRep 9 →* MulAut (QuaternionGroup 2)}
    (e : G ≃* SemidirectProduct (QuaternionGroup 2) (CyclicRep 9) φ) :
    order72Sylow2NormalRepCases G := by
  rcases q8_c9_semidirect_cases φ with h | h
  · obtain ⟨eh⟩ := h
    exact order72RepCases_q8_c9_prod
      ⟨e.trans (eh.trans SemidirectProduct.mulEquivProd)⟩
  · obtain ⟨eh⟩ := h
    exact order72RepCases_q8_c9 ⟨e.trans eh⟩

private theorem order72_classification_of_q8_e9_action {G : Type*} [Group G]
    {φ : ElemAbelianRep 3 →* MulAut (QuaternionGroup 2)}
    (e : G ≃* SemidirectProduct (QuaternionGroup 2) (ElemAbelianRep 3) φ) :
    order72Sylow2NormalRepCases G := by
  rcases q8_e9_semidirect_cases φ with h | h
  · obtain ⟨eh⟩ := h
    exact order72RepCases_q8_e9_prod
      ⟨e.trans (eh.trans SemidirectProduct.mulEquivProd)⟩
  · obtain ⟨eh⟩ := h
    exact order72RepCases_q8_e9 ⟨e.trans eh⟩

private theorem order72_classification_of_e8_c9_action {G : Type*} [Group G]
    {φ : CyclicRep 9 →* MulAut E8}
    (e : G ≃* SemidirectProduct E8 (CyclicRep 9) φ) :
    order72Sylow2NormalRepCases G := by
  rcases e8_c9_semidirect_cases φ with h | h
  · obtain ⟨eh⟩ := h
    exact order72RepCases_e8_c9_prod
      ⟨e.trans (eh.trans SemidirectProduct.mulEquivProd)⟩
  · obtain ⟨eh⟩ := h
    exact order72RepCases_e8_c9 ⟨e.trans eh⟩

private theorem order72_classification_of_e8_e9_action {G : Type*} [Group G]
    {φ : ElemAbelianRep 3 →* MulAut E8}
    (e : G ≃* SemidirectProduct E8 (ElemAbelianRep 3) φ) :
    order72Sylow2NormalRepCases G := by
  rcases e8_e9_semidirect_cases φ with h | h
  · obtain ⟨eh⟩ := h
    exact order72RepCases_e8_e9_prod
      ⟨e.trans (eh.trans SemidirectProduct.mulEquivProd)⟩
  · obtain ⟨eh⟩ := h
    exact order72RepCases_e8_e9 ⟨e.trans eh⟩

/-! ### Standard semidirect-product reduction of the Sylow-`3`-normal branch. -/

abbrev order72Sylow3NormalSemidirectCases (G : Type*) [Group G] : Prop :=
  (∃ φ : Multiplicative (ZMod 8) →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (Multiplicative (ZMod 8)) φ)) ∨
    (∃ φ : H2 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) H2 φ)) ∨
    (∃ φ : E8 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) E8 φ)) ∨
    (∃ φ : DihedralGroup 4 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ)) ∨
    (∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)) ∨
    (∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) ∨
    (∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) ∨
    (∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ))

private theorem order72Sylow3Cases_c9_c8 {G : Type*} [Group G]
    (h : ∃ φ : Multiplicative (ZMod 8) →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (Multiplicative (ZMod 8)) φ)) :
    order72Sylow3NormalSemidirectCases G :=
  Or.inl h

private theorem order72Sylow3Cases_c9_h2 {G : Type*} [Group G]
    (h : ∃ φ : H2 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) H2 φ)) :
    order72Sylow3NormalSemidirectCases G := by
  right
  left
  exact h

private theorem order72Sylow3Cases_c9_e8 {G : Type*} [Group G]
    (h : ∃ φ : E8 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) E8 φ)) :
    order72Sylow3NormalSemidirectCases G := by
  right
  right
  left
  exact h

private theorem order72Sylow3Cases_c9_d4 {G : Type*} [Group G]
    (h : ∃ φ : DihedralGroup 4 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ)) :
    order72Sylow3NormalSemidirectCases G := by
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Cases_c9_q8 {G : Type*} [Group G]
    (h : ∃ φ : QuaternionGroup 2 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ)) :
    order72Sylow3NormalSemidirectCases G := by
  right
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Cases_e9_c8 {G : Type*} [Group G]
    (h : ∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)) :
    order72Sylow3NormalSemidirectCases G := by
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Cases_e9_h2 {G : Type*} [Group G]
    (h : ∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) :
    order72Sylow3NormalSemidirectCases G := by
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Cases_e9_e8 {G : Type*} [Group G]
    (h : ∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) :
    order72Sylow3NormalSemidirectCases G := by
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Cases_e9_d4 {G : Type*} [Group G]
    (h : ∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) :
    order72Sylow3NormalSemidirectCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Cases_e9_q8 {G : Type*} [Group G]
    (h : ∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ)) :
    order72Sylow3NormalSemidirectCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  right
  exact h

abbrev order72Sylow3NormalSolvedC9Cases (G : Type*) [Group G] : Prop :=
  Nonempty (G ≃* CyclicRep 9 × Multiplicative (ZMod 8)) ∨
    Nonempty (G ≃* order72_C9_C8_inv) ∨
    Nonempty (G ≃* CyclicRep 9 × H2) ∨
    Nonempty (G ≃* order72_C9_H2_fstInv) ∨
    Nonempty (G ≃* order72_C9_H2_sndInv) ∨
    Nonempty (G ≃* order72_C9_H2_prodInv)

abbrev order72Sylow3NormalRemainingSemidirectCases (G : Type*) [Group G] : Prop :=
  (∃ φ : E8 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) E8 φ)) ∨
    (∃ φ : DihedralGroup 4 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ)) ∨
    (∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)) ∨
    (∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) ∨
    (∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) ∨
    (∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ))

abbrev order72Sylow3NormalPartialRepCases (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9Cases G ∨
    order72Sylow3NormalRemainingSemidirectCases G

private theorem order72Sylow3Partial_c9_c8_prod {G : Type*} [Group G]
    (h : Nonempty (G ≃* CyclicRep 9 × Multiplicative (ZMod 8))) :
    order72Sylow3NormalPartialRepCases G := by
  left
  left
  exact h

private theorem order72Sylow3Partial_c9_c8_inv {G : Type*} [Group G]
    (h : Nonempty (G ≃* order72_C9_C8_inv)) :
    order72Sylow3NormalPartialRepCases G := by
  left
  right
  left
  exact h

private theorem order72Sylow3Partial_c9_h2_prod {G : Type*} [Group G]
    (h : Nonempty (G ≃* CyclicRep 9 × H2)) :
    order72Sylow3NormalPartialRepCases G := by
  left
  right
  right
  left
  exact h

private theorem order72Sylow3Partial_c9_h2_fstInv {G : Type*} [Group G]
    (h : Nonempty (G ≃* order72_C9_H2_fstInv)) :
    order72Sylow3NormalPartialRepCases G := by
  left
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Partial_c9_h2_sndInv {G : Type*} [Group G]
    (h : Nonempty (G ≃* order72_C9_H2_sndInv)) :
    order72Sylow3NormalPartialRepCases G := by
  left
  right
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Partial_c9_h2_prodInv {G : Type*} [Group G]
    (h : Nonempty (G ≃* order72_C9_H2_prodInv)) :
    order72Sylow3NormalPartialRepCases G := by
  left
  right
  right
  right
  right
  right
  exact h

private theorem order72Sylow3Partial_c9_e8 {G : Type*} [Group G]
    (h : ∃ φ : E8 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) E8 φ)) :
    order72Sylow3NormalPartialRepCases G := by
  right
  left
  exact h

private theorem order72Sylow3Partial_c9_d4 {G : Type*} [Group G]
    (h : ∃ φ : DihedralGroup 4 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ)) :
    order72Sylow3NormalPartialRepCases G := by
  right
  right
  left
  exact h

private theorem order72Sylow3Partial_c9_q8 {G : Type*} [Group G]
    (h : ∃ φ : QuaternionGroup 2 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ)) :
    order72Sylow3NormalPartialRepCases G := by
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Partial_e9_c8 {G : Type*} [Group G]
    (h : ∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)) :
    order72Sylow3NormalPartialRepCases G := by
  right
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Partial_e9_h2 {G : Type*} [Group G]
    (h : ∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) :
    order72Sylow3NormalPartialRepCases G := by
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Partial_e9_e8 {G : Type*} [Group G]
    (h : ∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) :
    order72Sylow3NormalPartialRepCases G := by
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Partial_e9_d4 {G : Type*} [Group G]
    (h : ∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) :
    order72Sylow3NormalPartialRepCases G := by
  right
  right
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72Sylow3Partial_e9_q8 {G : Type*} [Group G]
    (h : ∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ)) :
    order72Sylow3NormalPartialRepCases G := by
  right
  right
  right
  right
  right
  right
  right
  right
  exact h

theorem order72_sylow3_semidirect_cases_refined {G : Type*} [Group G] :
    order72Sylow3NormalSemidirectCases G → order72Sylow3NormalPartialRepCases G := by
  intro hcases
  rcases hcases with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨φ, ⟨e⟩⟩ := h
    rcases order72_c9_c8_branch_cases e with hprod | hinv
    · exact order72Sylow3Partial_c9_c8_prod hprod
    · exact order72Sylow3Partial_c9_c8_inv hinv
  · obtain ⟨φ, ⟨e⟩⟩ := h
    rcases order72_c9_h2_branch_cases e with hprod | hfst | hsnd | hprodInv
    · exact order72Sylow3Partial_c9_h2_prod hprod
    · exact order72Sylow3Partial_c9_h2_fstInv hfst
    · exact order72Sylow3Partial_c9_h2_sndInv hsnd
    · exact order72Sylow3Partial_c9_h2_prodInv hprodInv
  · exact order72Sylow3Partial_c9_e8 h
  · exact order72Sylow3Partial_c9_d4 h
  · exact order72Sylow3Partial_c9_q8 h
  · exact order72Sylow3Partial_e9_c8 h
  · exact order72Sylow3Partial_e9_h2 h
  · exact order72Sylow3Partial_e9_e8 h
  · exact order72Sylow3Partial_e9_d4 h
  · exact order72Sylow3Partial_e9_q8 h

abbrev order72Sylow3NormalRemainingSemidirectCasesC9E8Done (G : Type*) [Group G] : Prop :=
  (∃ φ : DihedralGroup 4 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ)) ∨
    (∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)) ∨
    (∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) ∨
    (∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) ∨
    (∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ))

abbrev order72Sylow3NormalPartialRepCasesC9E8Done (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9Cases G ∨
    Nonempty (G ≃* CyclicRep 9 × E8) ∨
      Nonempty (G ≃* order72_C9_E8_inv100) ∨
        order72Sylow3NormalRemainingSemidirectCasesC9E8Done G

private theorem order72RemainingC9E8Done_c9_d4 {G : Type*} [Group G]
    (h : ∃ φ : DihedralGroup 4 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Done G :=
  Or.inl h

private theorem order72RemainingC9E8Done_c9_q8 {G : Type*} [Group G]
    (h : ∃ φ : QuaternionGroup 2 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (QuaternionGroup 2) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Done G := by
  right
  left
  exact h

private theorem order72RemainingC9E8Done_e9_c8 {G : Type*} [Group G]
    (h : ∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Done G := by
  right
  right
  left
  exact h

private theorem order72RemainingC9E8Done_e9_h2 {G : Type*} [Group G]
    (h : ∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Done G := by
  right
  right
  right
  left
  exact h

private theorem order72RemainingC9E8Done_e9_e8 {G : Type*} [Group G]
    (h : ∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Done G := by
  right
  right
  right
  right
  left
  exact h

private theorem order72RemainingC9E8Done_e9_d4 {G : Type*} [Group G]
    (h : ∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Done G := by
  right
  right
  right
  right
  right
  left
  exact h

private theorem order72RemainingC9E8Done_e9_q8 {G : Type*} [Group G]
    (h : ∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Done G := by
  right
  right
  right
  right
  right
  right
  exact h

private theorem order72PartialC9E8Done_of_partial {G : Type*} [Group G] :
    order72Sylow3NormalPartialRepCases G →
      order72Sylow3NormalPartialRepCasesC9E8Done G := by
  intro hcases
  rcases hcases with hsolved | hremaining
  · left
    exact hsolved
  · rcases hremaining with h | h | h | h | h | h | h | h
    · obtain ⟨φ, ⟨e⟩⟩ := h
      rcases order72_c9_e8_branch_cases_standard e with hprod | hinv
      · right
        left
        exact hprod
      · right
        right
        left
        exact hinv
    · right
      right
      right
      exact order72RemainingC9E8Done_c9_d4 h
    · right
      right
      right
      exact order72RemainingC9E8Done_c9_q8 h
    · right
      right
      right
      exact order72RemainingC9E8Done_e9_c8 h
    · right
      right
      right
      exact order72RemainingC9E8Done_e9_h2 h
    · right
      right
      right
      exact order72RemainingC9E8Done_e9_e8 h
    · right
      right
      right
      exact order72RemainingC9E8Done_e9_d4 h
    · right
      right
      right
      exact order72RemainingC9E8Done_e9_q8 h

theorem order72_sylow3_semidirect_cases_refined_c9_e8_done {G : Type*} [Group G] :
    order72Sylow3NormalSemidirectCases G →
      order72Sylow3NormalPartialRepCasesC9E8Done G := by
  intro hcases
  exact order72PartialC9E8Done_of_partial
    (order72_sylow3_semidirect_cases_refined hcases)

abbrev order72Sylow3NormalRemainingSemidirectCasesC9E8Q8Done (G : Type*) [Group G] : Prop :=
  (∃ φ : DihedralGroup 4 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ)) ∨
    (∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)) ∨
    (∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) ∨
    (∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) ∨
    (∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ))

abbrev order72Sylow3NormalPartialRepCasesC9E8Q8Done (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9Cases G ∨
    Nonempty (G ≃* CyclicRep 9 × E8) ∨
      Nonempty (G ≃* order72_C9_E8_inv100) ∨
        Nonempty (G ≃* CyclicRep 9 × QuaternionGroup 2) ∨
          Nonempty (G ≃* order72_C9_Q8_invA) ∨
            order72Sylow3NormalRemainingSemidirectCasesC9E8Q8Done G

private theorem order72RemainingC9E8Q8Done_c9_d4 {G : Type*} [Group G]
    (h : ∃ φ : DihedralGroup 4 →* MulAut (CyclicRep 9),
      Nonempty (G ≃* SemidirectProduct (CyclicRep 9) (DihedralGroup 4) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Q8Done G :=
  Or.inl h

private theorem order72RemainingC9E8Q8Done_e9_c8 {G : Type*} [Group G]
    (h : ∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Q8Done G := by
  right
  left
  exact h

private theorem order72RemainingC9E8Q8Done_e9_h2 {G : Type*} [Group G]
    (h : ∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Q8Done G := by
  right
  right
  left
  exact h

private theorem order72RemainingC9E8Q8Done_e9_e8 {G : Type*} [Group G]
    (h : ∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Q8Done G := by
  right
  right
  right
  left
  exact h

private theorem order72RemainingC9E8Q8Done_e9_d4 {G : Type*} [Group G]
    (h : ∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Q8Done G := by
  right
  right
  right
  right
  left
  exact h

private theorem order72RemainingC9E8Q8Done_e9_q8 {G : Type*} [Group G]
    (h : ∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9E8Q8Done G := by
  right
  right
  right
  right
  right
  exact h

private theorem order72PartialC9E8Q8Done_of_c9_e8_done {G : Type*} [Group G] :
    order72Sylow3NormalPartialRepCasesC9E8Done G →
      order72Sylow3NormalPartialRepCasesC9E8Q8Done G := by
  intro hcases
  rcases hcases with hsolved | hE8prod | hE8inv | hremaining
  · left
    exact hsolved
  · right
    left
    exact hE8prod
  · right
    right
    left
    exact hE8inv
  · rcases hremaining with h | h | h | h | h | h | h
    · right
      right
      right
      right
      right
      exact order72RemainingC9E8Q8Done_c9_d4 h
    · obtain ⟨φ, ⟨e⟩⟩ := h
      rcases order72_c9_q8_branch_cases_standard e with hprod | hinv
      · right
        right
        right
        left
        exact hprod
      · right
        right
        right
        right
        left
        exact hinv
    · right
      right
      right
      right
      right
      exact order72RemainingC9E8Q8Done_e9_c8 h
    · right
      right
      right
      right
      right
      exact order72RemainingC9E8Q8Done_e9_h2 h
    · right
      right
      right
      right
      right
      exact order72RemainingC9E8Q8Done_e9_e8 h
    · right
      right
      right
      right
      right
      exact order72RemainingC9E8Q8Done_e9_d4 h
    · right
      right
      right
      right
      right
      exact order72RemainingC9E8Q8Done_e9_q8 h

theorem order72_sylow3_semidirect_cases_refined_c9_e8_q8_done {G : Type*} [Group G] :
    order72Sylow3NormalSemidirectCases G →
      order72Sylow3NormalPartialRepCasesC9E8Q8Done G := by
  intro hcases
  exact order72PartialC9E8Q8Done_of_c9_e8_done
    (order72_sylow3_semidirect_cases_refined_c9_e8_done hcases)

abbrev order72Sylow3NormalRemainingSemidirectCasesC9AllDone (G : Type*) [Group G] : Prop :=
  (∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)) ∨
    (∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) ∨
    (∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) ∨
    (∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ))

abbrev order72Sylow3NormalPartialRepCasesC9AllDone (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9Cases G ∨
    Nonempty (G ≃* CyclicRep 9 × E8) ∨
      Nonempty (G ≃* order72_C9_E8_inv100) ∨
        Nonempty (G ≃* CyclicRep 9 × QuaternionGroup 2) ∨
          Nonempty (G ≃* order72_C9_Q8_invA) ∨
            Nonempty (G ≃* CyclicRep 9 × DihedralGroup 4) ∨
              Nonempty (G ≃* order72_C9_D4_invRot) ∨
                Nonempty (G ≃* order72_C9_D4_invRef) ∨
                  order72Sylow3NormalRemainingSemidirectCasesC9AllDone G

private theorem order72RemainingC9AllDone_e9_c8 {G : Type*} [Group G]
    (h : ∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9AllDone G :=
  Or.inl h

private theorem order72RemainingC9AllDone_e9_h2 {G : Type*} [Group G]
    (h : ∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9AllDone G := by
  right
  left
  exact h

private theorem order72RemainingC9AllDone_e9_e8 {G : Type*} [Group G]
    (h : ∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9AllDone G := by
  right
  right
  left
  exact h

private theorem order72RemainingC9AllDone_e9_d4 {G : Type*} [Group G]
    (h : ∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9AllDone G := by
  right
  right
  right
  left
  exact h

private theorem order72RemainingC9AllDone_e9_q8 {G : Type*} [Group G]
    (h : ∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ)) :
    order72Sylow3NormalRemainingSemidirectCasesC9AllDone G := by
  right
  right
  right
  right
  exact h

private theorem order72PartialC9AllDone_of_c9_e8_q8_done {G : Type*} [Group G] :
    order72Sylow3NormalPartialRepCasesC9E8Q8Done G →
      order72Sylow3NormalPartialRepCasesC9AllDone G := by
  intro hcases
  rcases hcases with hsolved | hE8prod | hE8inv | hQ8prod | hQ8inv | hremaining
  · left
    exact hsolved
  · right
    left
    exact hE8prod
  · right
    right
    left
    exact hE8inv
  · right
    right
    right
    left
    exact hQ8prod
  · right
    right
    right
    right
    left
    exact hQ8inv
  · rcases hremaining with h | h | h | h | h | h
    · obtain ⟨φ, ⟨e⟩⟩ := h
      rcases order72_c9_d4_branch_cases_standard e with hprod | hrot | href
      · right
        right
        right
        right
        right
        left
        exact hprod
      · right
        right
        right
        right
        right
        right
        left
        exact hrot
      · right
        right
        right
        right
        right
        right
        right
        left
        exact href
    · right
      right
      right
      right
      right
      right
      right
      right
      exact order72RemainingC9AllDone_e9_c8 h
    · right
      right
      right
      right
      right
      right
      right
      right
      exact order72RemainingC9AllDone_e9_h2 h
    · right
      right
      right
      right
      right
      right
      right
      right
      exact order72RemainingC9AllDone_e9_e8 h
    · right
      right
      right
      right
      right
      right
      right
      right
      exact order72RemainingC9AllDone_e9_d4 h
    · right
      right
      right
      right
      right
      right
      right
      right
      exact order72RemainingC9AllDone_e9_q8 h

theorem order72_sylow3_semidirect_cases_refined_c9_all_done {G : Type*} [Group G] :
    order72Sylow3NormalSemidirectCases G →
      order72Sylow3NormalPartialRepCasesC9AllDone G := by
  intro hcases
  exact order72PartialC9AllDone_of_c9_e8_q8_done
    (order72_sylow3_semidirect_cases_refined_c9_e8_q8_done hcases)

abbrev order72Sylow3NormalSolvedC9AllCases (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9Cases G ∨
    Nonempty (G ≃* CyclicRep 9 × E8) ∨
      Nonempty (G ≃* order72_C9_E8_inv100) ∨
        Nonempty (G ≃* CyclicRep 9 × QuaternionGroup 2) ∨
          Nonempty (G ≃* order72_C9_Q8_invA) ∨
            Nonempty (G ≃* CyclicRep 9 × DihedralGroup 4) ∨
              Nonempty (G ≃* order72_C9_D4_invRot) ∨
                Nonempty (G ≃* order72_C9_D4_invRef)

abbrev order72Sylow3NormalRemainingSemidirectCasesC9AllE9C8RepsListed
    (G : Type*) [Group G] : Prop :=
  (∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ) ∧
      φ ≠ 1 ∧ φ ≠ order72_e9C8NegAction ∧ φ ≠ order72_e9C8ReflectAction ∧
        φ ≠ order72_e9C8Order4Action ∧ φ ≠ order72_e9C8Order8Action) ∨
    (∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) ∨
    (∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) ∨
    (∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ))

abbrev order72Sylow3NormalPartialRepCasesC9AllE9C8RepsListed
    (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9AllCases G ∨
    Nonempty (G ≃* ElemAbelianRep 3 × Multiplicative (ZMod 8)) ∨
      Nonempty (G ≃* order72_E9_C8_neg) ∨
        Nonempty (G ≃* order72_E9_C8_reflect) ∨
          Nonempty (G ≃* order72_E9_C8_order4) ∨
            Nonempty (G ≃* order72_E9_C8_order8) ∨
              order72Sylow3NormalRemainingSemidirectCasesC9AllE9C8RepsListed G

private theorem order72PartialC9AllE9C8RepsListed_of_c9_all_done {G : Type*} [Group G] :
    order72Sylow3NormalPartialRepCasesC9AllDone G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8RepsListed G := by
  intro hcases
  rcases hcases with hsolved | hE8prod | hE8inv | hQ8prod | hQ8inv |
    hD4prod | hD4rot | hD4ref | hremaining
  · left
    left
    exact hsolved
  · left
    right
    left
    exact hE8prod
  · left
    right
    right
    left
    exact hE8inv
  · left
    right
    right
    right
    left
    exact hQ8prod
  · left
    right
    right
    right
    right
    left
    exact hQ8inv
  · left
    right
    right
    right
    right
    right
    left
    exact hD4prod
  · left
    right
    right
    right
    right
    right
    right
    left
    exact hD4rot
  · left
    right
    right
    right
    right
    right
    right
    right
    exact hD4ref
  · rcases hremaining with hC8 | hH2 | hE8 | hD4 | hQ8
    · obtain ⟨φ, hφ⟩ := hC8
      by_cases htriv : φ = 1
      · obtain ⟨e⟩ := hφ
        right
        left
        exact ⟨e.trans ((semidirectProductCongr_eq htriv).trans
          SemidirectProduct.mulEquivProd)⟩
      · by_cases hneg : φ = order72_e9C8NegAction
        · obtain ⟨e⟩ := hφ
          right
          right
          left
          exact ⟨e.trans (semidirectProductCongr_eq hneg)⟩
        · by_cases href : φ = order72_e9C8ReflectAction
          · obtain ⟨e⟩ := hφ
            right
            right
            right
            left
            exact ⟨e.trans (semidirectProductCongr_eq href)⟩
          · by_cases h4 : φ = order72_e9C8Order4Action
            · obtain ⟨e⟩ := hφ
              right
              right
              right
              right
              left
              exact ⟨e.trans (semidirectProductCongr_eq h4)⟩
            · by_cases h8 : φ = order72_e9C8Order8Action
              · obtain ⟨e⟩ := hφ
                right
                right
                right
                right
                right
                left
                exact ⟨e.trans (semidirectProductCongr_eq h8)⟩
              · right
                right
                right
                right
                right
                right
                left
                exact ⟨φ, hφ, htriv, hneg, href, h4, h8⟩
    · right
      right
      right
      right
      right
      right
      right
      left
      exact hH2
    · right
      right
      right
      right
      right
      right
      right
      right
      left
      exact hE8
    · right
      right
      right
      right
      right
      right
      right
      right
      right
      left
      exact hD4
    · right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact hQ8

theorem order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_reps_listed
    {G : Type*} [Group G] :
    order72Sylow3NormalSemidirectCases G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8RepsListed G := by
  intro hcases
  exact order72PartialC9AllE9C8RepsListed_of_c9_all_done
    (order72_sylow3_semidirect_cases_refined_c9_all_done hcases)

abbrev order72Sylow3NormalRemainingSemidirectCasesC9AllE9C8OddRepsDone
    (G : Type*) [Group G] : Prop :=
  (∃ φ : Multiplicative (ZMod 8) →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (Multiplicative (ZMod 8)) φ) ∧
      φ (Multiplicative.ofAdd (1 : ZMod 8)) ≠ 1 ∧
      φ (Multiplicative.ofAdd (1 : ZMod 8)) ≠ order72_E9_negAut ∧
      φ (Multiplicative.ofAdd (1 : ZMod 8)) ≠ order72_E9_reflectAut ∧
      φ (Multiplicative.ofAdd (1 : ZMod 8)) ≠ order72_E9_order4Aut ∧
      φ (Multiplicative.ofAdd (1 : ZMod 8)) ≠ order72_E9_order4Aut ^ 3 ∧
      φ (Multiplicative.ofAdd (1 : ZMod 8)) ≠ order72_E9_order8Aut ∧
      φ (Multiplicative.ofAdd (1 : ZMod 8)) ≠ order72_E9_order8Aut ^ 3 ∧
      φ (Multiplicative.ofAdd (1 : ZMod 8)) ≠ order72_E9_order8Aut ^ 5 ∧
      φ (Multiplicative.ofAdd (1 : ZMod 8)) ≠ order72_E9_order8Aut ^ 7) ∨
    (∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) ∨
    (∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) ∨
    (∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ))

abbrev order72Sylow3NormalPartialRepCasesC9AllE9C8OddRepsDone
    (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9AllCases G ∨
    Nonempty (G ≃* ElemAbelianRep 3 × Multiplicative (ZMod 8)) ∨
      Nonempty (G ≃* order72_E9_C8_neg) ∨
        Nonempty (G ≃* order72_E9_C8_reflect) ∨
          Nonempty (G ≃* order72_E9_C8_order4) ∨
            Nonempty (G ≃* order72_E9_C8_order8) ∨
              order72Sylow3NormalRemainingSemidirectCasesC9AllE9C8OddRepsDone G

private theorem order72PartialC9AllE9C8OddRepsDone_of_reps_listed {G : Type*} [Group G] :
    order72Sylow3NormalPartialRepCasesC9AllE9C8RepsListed G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8OddRepsDone G := by
  intro hcases
  rcases hcases with hsolved | hprod | hneg | href | h4 | h8 | hremaining
  · left
    exact hsolved
  · right
    left
    exact hprod
  · right
    right
    left
    exact hneg
  · right
    right
    right
    left
    exact href
  · right
    right
    right
    right
    left
    exact h4
  · right
    right
    right
    right
    right
    left
    exact h8
  · rcases hremaining with hC8 | hH2 | hE8 | hD4 | hQ8
    · obtain ⟨φ, hφ, _hne1, _hneneg, _hnereflect, _hne4, _hne8⟩ := hC8
      by_cases h1 : φ (Multiplicative.ofAdd (1 : ZMod 8)) = 1
      · right
        left
        obtain ⟨e⟩ := hφ
        obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_eq_one φ h1
        exact ⟨e.trans eh⟩
      · by_cases hneg : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_negAut
        · right
          right
          left
          obtain ⟨e⟩ := hφ
          obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_eq_neg φ hneg
          exact ⟨e.trans eh⟩
        · by_cases href : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_reflectAut
          · right
            right
            right
            left
            obtain ⟨e⟩ := hφ
            obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_eq_reflect φ href
            exact ⟨e.trans eh⟩
          · by_cases h4 : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order4Aut
            · right
              right
              right
              right
              left
              obtain ⟨e⟩ := hφ
              obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_eq_order4 φ h4
              exact ⟨e.trans eh⟩
            · by_cases h43 :
                φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order4Aut ^ 3
              · right
                right
                right
                right
                left
                obtain ⟨e⟩ := hφ
                obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_eq_order4_pow3 φ h43
                exact ⟨e.trans eh⟩
              · by_cases h8 : φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut
                · right
                  right
                  right
                  right
                  right
                  left
                  obtain ⟨e⟩ := hφ
                  obtain ⟨eh⟩ := order72_e9_c8_semidirect_case_of_gen_eq_order8 φ h8
                  exact ⟨e.trans eh⟩
                · by_cases h83 :
                    φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut ^ 3
                  · right
                    right
                    right
                    right
                    right
                    left
                    obtain ⟨e⟩ := hφ
                    obtain ⟨eh⟩ :=
                      order72_e9_c8_semidirect_case_of_gen_eq_order8_pow3 φ h83
                    exact ⟨e.trans eh⟩
                  · by_cases h85 :
                      φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut ^ 5
                    · right
                      right
                      right
                      right
                      right
                      left
                      obtain ⟨e⟩ := hφ
                      obtain ⟨eh⟩ :=
                        order72_e9_c8_semidirect_case_of_gen_eq_order8_pow5 φ h85
                      exact ⟨e.trans eh⟩
                    · by_cases h87 :
                        φ (Multiplicative.ofAdd (1 : ZMod 8)) = order72_E9_order8Aut ^ 7
                      · right
                        right
                        right
                        right
                        right
                        left
                        obtain ⟨e⟩ := hφ
                        obtain ⟨eh⟩ :=
                          order72_e9_c8_semidirect_case_of_gen_eq_order8_pow7 φ h87
                        exact ⟨e.trans eh⟩
                      · right
                        right
                        right
                        right
                        right
                        right
                        left
                        exact ⟨φ, hφ, h1, hneg, href, h4, h43, h8, h83, h85, h87⟩
    · right
      right
      right
      right
      right
      right
      right
      left
      exact hH2
    · right
      right
      right
      right
      right
      right
      right
      right
      left
      exact hE8
    · right
      right
      right
      right
      right
      right
      right
      right
      right
      left
      exact hD4
    · right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact hQ8

theorem order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_odd_reps_done
    {G : Type*} [Group G] :
    order72Sylow3NormalSemidirectCases G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8OddRepsDone G := by
  intro hcases
  exact order72PartialC9AllE9C8OddRepsDone_of_reps_listed
    (order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_reps_listed hcases)

/-- If the Sylow `3`-subgroup is normal, Schur-Zassenhaus and the order-`9`/order-`8`
classification reduce the group to one of ten standard semidirect-product action problems. -/
theorem order72_semidirectProduct_standard_cases_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalSemidirectCases G := by
  obtain ⟨N, K, φ, _hNnormal, hcardN, hcardK, ⟨e⟩⟩ :=
    order72_semidirectProduct_of_sylow_three_normal hG hSyl
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fintype N := Fintype.ofFinite N
  haveI : Fintype K := Fintype.ofFinite K
  have hcardN' : Nat.card N = 3 ^ 2 := hcardN.trans (by norm_num)
  rcases prime_sq_classification (p := 3) hcardN' with hN | hN
  · obtain ⟨eN⟩ := hN
    rcases P3Group.classification 2 K (hcardK.trans (by norm_num)) with
      hK | hK | hK | hK | hK | hK | hK
    · change Nonempty (K ≃* Multiplicative (ZMod 8)) at hK
      obtain ⟨eK⟩ := hK
      exact order72Sylow3Cases_c9_c8 ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eK)⟩⟩
    · change Nonempty (K ≃* H2) at hK
      obtain ⟨eK⟩ := hK
      exact order72Sylow3Cases_c9_h2 ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eK)⟩⟩
    · change Nonempty (K ≃* E8) at hK
      obtain ⟨eK⟩ := hK
      exact order72Sylow3Cases_c9_e8 ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eK)⟩⟩
    · exact (hK.1 rfl).elim
    · exact (hK.1 rfl).elim
    · obtain ⟨eK⟩ := hK.2
      exact order72Sylow3Cases_c9_d4 ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eK)⟩⟩
    · obtain ⟨eK⟩ := hK.2
      exact order72Sylow3Cases_c9_q8 ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eK)⟩⟩
  · obtain ⟨eN⟩ := hN
    rcases P3Group.classification 2 K (hcardK.trans (by norm_num)) with
      hK | hK | hK | hK | hK | hK | hK
    · change Nonempty (K ≃* Multiplicative (ZMod 8)) at hK
      obtain ⟨eK⟩ := hK
      exact order72Sylow3Cases_e9_c8 ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eK)⟩⟩
    · change Nonempty (K ≃* H2) at hK
      obtain ⟨eK⟩ := hK
      exact order72Sylow3Cases_e9_h2 ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eK)⟩⟩
    · change Nonempty (K ≃* E8) at hK
      obtain ⟨eK⟩ := hK
      exact order72Sylow3Cases_e9_e8 ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eK)⟩⟩
    · exact (hK.1 rfl).elim
    · exact (hK.1 rfl).elim
    · obtain ⟨eK⟩ := hK.2
      exact order72Sylow3Cases_e9_d4 ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eK)⟩⟩
    · obtain ⟨eK⟩ := hK.2
      exact order72Sylow3Cases_e9_q8 ⟨_, ⟨e.trans (SemidirectProduct.congr' eN eK)⟩⟩

/-- A refined form of the Sylow-`3`-normal branch: the `C9 ⋊ C8` and `C9 ⋊ H2`
subbranches have been classified into explicit representatives; the remaining branches are
kept as semidirect-product action problems. -/
theorem order72_partial_rep_cases_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalPartialRepCases G :=
  order72_sylow3_semidirect_cases_refined
    (order72_semidirectProduct_standard_cases_of_sylow_three_normal hG hSyl)

/-- Further refined Sylow-`3`-normal branch: in addition to `C9 ⋊ C8` and `C9 ⋊ H2`,
the `C9 ⋊ E8` branch has been classified into the direct product and one standard nontrivial
sign-character representative. -/
theorem order72_partial_rep_cases_c9_e8_done_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalPartialRepCasesC9E8Done G :=
  order72_sylow3_semidirect_cases_refined_c9_e8_done
    (order72_semidirectProduct_standard_cases_of_sylow_three_normal hG hSyl)

/-- Further refined Sylow-`3`-normal branch: the `C9 ⋊ Q8` branch has also been reduced
to the direct product and one standard nontrivial sign-character representative. -/
theorem order72_partial_rep_cases_c9_e8_q8_done_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalPartialRepCasesC9E8Q8Done G :=
  order72_sylow3_semidirect_cases_refined_c9_e8_q8_done
    (order72_semidirectProduct_standard_cases_of_sylow_three_normal hG hSyl)

/-- Further refined Sylow-`3`-normal branch: all `C9 ⋊ H` cases for `|H| = 8` have been
reduced to explicit representatives; only the `E9 ⋊ H` action problems remain. -/
theorem order72_partial_rep_cases_c9_all_done_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalPartialRepCasesC9AllDone G :=
  order72_sylow3_semidirect_cases_refined_c9_all_done
    (order72_semidirectProduct_standard_cases_of_sylow_three_normal hG hSyl)

/-- Further refined Sylow-`3`-normal branch: all `C9 ⋊ H` cases are explicit, and the
direct product plus four standard exact `E9 ⋊ C8` actions are split out from the remaining
`E9` action problems. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_reps_listed_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8RepsListed G :=
  order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_reps_listed
    (order72_semidirectProduct_standard_cases_of_sylow_three_normal hG hSyl)

/-- Further refined Sylow-`3`-normal branch: all `C9 ⋊ H` cases are explicit, and the
direct product plus the standard `E9 ⋊ C8` actions are split out even when the `C8` generator
is replaced by an odd power. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_odd_reps_done_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8OddRepsDone G :=
  order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_odd_reps_done
    (order72_semidirectProduct_standard_cases_of_sylow_three_normal hG hSyl)

/-- If the Sylow `2`-subgroup is normal, the group falls into the fully classified
`H ⋊ K` branch with `|H| = 8` and `|K| = 9`. -/
theorem order72_classification_of_sylow_two_normal {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 2 G, (↑P : Subgroup G).Normal) :
    order72Sylow2NormalRepCases G := by
  obtain ⟨N, K, φ, _hNnormal, hcardN, hcardK, ⟨e⟩⟩ :=
    order72_semidirectProduct_of_sylow_two_normal hG hSyl
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fintype N := Fintype.ofFinite N
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK' : Nat.card K = 3 ^ 2 := hcardK.trans (by norm_num)
  rcases P3Group.classification 2 N (hcardN.trans (by norm_num)) with
    hN | hN | hN | hN | hN | hN | hN
  · change Nonempty (N ≃* Multiplicative (ZMod 8)) at hN
    obtain ⟨eN⟩ := hN
    rcases prime_sq_classification (p := 3) hcardK' with hK | hK
    · obtain ⟨eK⟩ := hK
      exact order72_classification_of_c8_c9_action
        (e.trans (SemidirectProduct.congr' eN eK))
    · obtain ⟨eK⟩ := hK
      exact order72_classification_of_c8_e9_action
        (e.trans (SemidirectProduct.congr' eN eK))
  · change Nonempty (N ≃* H2) at hN
    obtain ⟨eN⟩ := hN
    rcases prime_sq_classification (p := 3) hcardK' with hK | hK
    · obtain ⟨eK⟩ := hK
      exact order72_classification_of_h2_c9_action
        (e.trans (SemidirectProduct.congr' eN eK))
    · obtain ⟨eK⟩ := hK
      exact order72_classification_of_h2_e9_action
        (e.trans (SemidirectProduct.congr' eN eK))
  · change Nonempty (N ≃* E8) at hN
    obtain ⟨eN⟩ := hN
    rcases prime_sq_classification (p := 3) hcardK' with hK | hK
    · obtain ⟨eK⟩ := hK
      exact order72_classification_of_e8_c9_action
        (e.trans (SemidirectProduct.congr' eN eK))
    · obtain ⟨eK⟩ := hK
      exact order72_classification_of_e8_e9_action
        (e.trans (SemidirectProduct.congr' eN eK))
  · exact (hN.1 rfl).elim
  · exact (hN.1 rfl).elim
  · obtain ⟨eN⟩ := hN.2
    rcases prime_sq_classification (p := 3) hcardK' with hK | hK
    · obtain ⟨eK⟩ := hK
      exact order72_classification_of_d4_c9_action
        (e.trans (SemidirectProduct.congr' eN eK))
    · obtain ⟨eK⟩ := hK
      exact order72_classification_of_d4_e9_action
        (e.trans (SemidirectProduct.congr' eN eK))
  · obtain ⟨eN⟩ := hN.2
    rcases prime_sq_classification (p := 3) hcardK' with hK | hK
    · obtain ⟨eK⟩ := hK
      exact order72_classification_of_q8_c9_action
        (e.trans (SemidirectProduct.congr' eN eK))
    · obtain ⟨eK⟩ := hK
      exact order72_classification_of_q8_e9_action
        (e.trans (SemidirectProduct.congr' eN eK))

/-- The `n₂ = 1` case is exactly the completed Sylow-`2`-normal branch. -/
theorem order72_classification_of_card_sylow_two_eq_one {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 72) (hSyl : Nat.card (Sylow 2 G) = 1) :
    order72Sylow2NormalRepCases G := by
  exact order72_classification_of_sylow_two_normal hG
    (fun P => sylow_two_normal_of_card_sylow_two_eq_one hSyl P)

/-- The `n₃ = 1` case is the Sylow-`3`-normal semidirect-product branch. -/
theorem order72_semidirectProduct_standard_cases_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalSemidirectCases G := by
  exact order72_semidirectProduct_standard_cases_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- Refined `n₃ = 1` branch with the solved `C9 ⋊ C8` and `C9 ⋊ H2` action cases
expanded into explicit representatives. -/
theorem order72_partial_rep_cases_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalPartialRepCases G := by
  exact order72_partial_rep_cases_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- Refined `n₃ = 1` branch with the `C9 ⋊ E8` action cases also reduced to explicit
representatives. -/
theorem order72_partial_rep_cases_c9_e8_done_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalPartialRepCasesC9E8Done G := by
  exact order72_partial_rep_cases_c9_e8_done_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- Refined `n₃ = 1` branch with the `C9 ⋊ Q8` action cases also reduced to explicit
representatives. -/
theorem order72_partial_rep_cases_c9_e8_q8_done_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalPartialRepCasesC9E8Q8Done G := by
  exact order72_partial_rep_cases_c9_e8_q8_done_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- Refined `n₃ = 1` branch with all `C9 ⋊ H` cases for `|H| = 8` reduced to explicit
representatives. -/
theorem order72_partial_rep_cases_c9_all_done_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalPartialRepCasesC9AllDone G := by
  exact order72_partial_rep_cases_c9_all_done_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- Refined `n₃ = 1` branch with all `C9 ⋊ H` cases explicit and standard exact
`E9 ⋊ C8` actions split out. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_reps_listed_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8RepsListed G := by
  exact order72_partial_rep_cases_c9_all_e9_c8_reps_listed_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- Refined `n₃ = 1` branch with all `C9 ⋊ H` cases explicit and standard `E9 ⋊ C8`
actions split out up to odd powers of the `C8` generator. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_odd_reps_done_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8OddRepsDone G := by
  exact order72_partial_rep_cases_c9_all_e9_c8_odd_reps_done_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- The current top-level reduction for groups of order `72`: either the Sylow `3`-subgroup
has been reduced to ten standard semidirect-product action problems, or the Sylow `2`-normal
branch has already been classified into the representatives above, or one is in the residual
case `n₃ = 4` and `n₂ ≠ 1`. -/
theorem order72_partial_classification {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalSemidirectCases G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl (order72_semidirectProduct_standard_cases_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)

/-- A stronger current top-level reduction: the solved `C9 ⋊ C8` and `C9 ⋊ H2` parts of
the Sylow-`3`-normal branch are already expanded into explicit representatives. -/
theorem order72_partial_classification_refined {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 72) :
    order72Sylow3NormalPartialRepCases G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl (order72_partial_rep_cases_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)

/-- The strongest current top-level reduction: `C9 ⋊ C8`, `C9 ⋊ H2`, and `C9 ⋊ E8`
inside the Sylow-`3`-normal branch have been reduced to explicit representatives. -/
theorem order72_partial_classification_refined_c9_e8_done
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalPartialRepCasesC9E8Done G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl (order72_partial_rep_cases_c9_e8_done_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)

/-- Stronger top-level reduction with `C9 ⋊ C8`, `C9 ⋊ H2`, `C9 ⋊ E8`, and `C9 ⋊ Q8`
inside the Sylow-`3`-normal branch reduced to explicit representatives. -/
theorem order72_partial_classification_refined_c9_e8_q8_done
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalPartialRepCasesC9E8Q8Done G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl (order72_partial_rep_cases_c9_e8_q8_done_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)

/-- Strongest current top-level reduction: every `C9 ⋊ H` case in the Sylow-`3`-normal
branch has explicit representatives; the remaining semidirect action problems all have
normal subgroup `E9`. -/
theorem order72_partial_classification_refined_c9_all_done
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalPartialRepCasesC9AllDone G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl (order72_partial_rep_cases_c9_all_done_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)

/-- Current top-level reduction with all `C9 ⋊ H` cases explicit and the direct product
plus four standard exact `E9 ⋊ C8` actions split out from the remaining `E9` action
problems. -/
theorem order72_partial_classification_refined_c9_all_e9_c8_reps_listed
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8RepsListed G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl
      (order72_partial_rep_cases_c9_all_e9_c8_reps_listed_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)

/-- Current top-level reduction with all `C9 ⋊ H` cases explicit and the standard
`E9 ⋊ C8` representatives split out up to replacing the `C8` generator by an odd power. -/
theorem order72_partial_classification_refined_c9_all_e9_c8_odd_reps_done
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8OddRepsDone G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl
      (order72_partial_rep_cases_c9_all_e9_c8_odd_reps_done_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)

/-! ### The Sylow-`3`-normal branch with `E9 ⋊ C8` fully classified.

With the `9 × 9` generator-image enumeration (`order72_e9_c8_semidirect_cases`), the
`E9 ⋊ C8` cell contributes exactly five isomorphism classes: the direct product and the
four standard actions `order72_E9_C8_neg`, `order72_E9_C8_reflect`,
`order72_E9_C8_order4`, `order72_E9_C8_order8`.  The remaining action problems are
`E9 ⋊ H` for `H ∈ {H2, E8, D4, Q8}`. -/

/-- The fully classified part of the Sylow-`3`-normal branch after solving the
`E9 ⋊ C8` cell: the previous solved `C9 ⋊ H` cases together with the five
`E9 ⋊ C8` representatives. -/
abbrev order72Sylow3NormalSolvedC9AllE9C8Cases (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9AllCases G ∨
    Nonempty (G ≃* ElemAbelianRep 3 × Multiplicative (ZMod 8)) ∨
      Nonempty (G ≃* order72_E9_C8_neg) ∨
        Nonempty (G ≃* order72_E9_C8_reflect) ∨
          Nonempty (G ≃* order72_E9_C8_order4) ∨
            Nonempty (G ≃* order72_E9_C8_order8)

/-- The remaining action problems of the Sylow-`3`-normal branch: `E9 ⋊ H` with
`H ∈ {H2, E8, D4, Q8}`. -/
abbrev order72Sylow3NormalRemainingSemidirectCasesE9H2E8D4Q8 (G : Type*) [Group G] :
    Prop :=
  (∃ φ : H2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) H2 φ)) ∨
    (∃ φ : E8 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) E8 φ)) ∨
    (∃ φ : DihedralGroup 4 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (DihedralGroup 4) φ)) ∨
    (∃ φ : QuaternionGroup 2 →* MulAut (ElemAbelianRep 3),
      Nonempty (G ≃* SemidirectProduct (ElemAbelianRep 3) (QuaternionGroup 2) φ))

/-- The Sylow-`3`-normal branch with the `C9 ⋊ H` and `E9 ⋊ C8` cells fully classified:
the remaining cases are exactly the four `E9 ⋊ H` action problems. -/
abbrev order72Sylow3NormalPartialRepCasesC9AllE9C8Done (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedC9AllE9C8Cases G ∨
    order72Sylow3NormalRemainingSemidirectCasesE9H2E8D4Q8 G

private theorem order72PartialC9AllE9C8Done_of_odd_reps_done {G : Type*} [Group G] :
    order72Sylow3NormalPartialRepCasesC9AllE9C8OddRepsDone G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8Done G := by
  intro hcases
  rcases hcases with hsolved | hprod | hneg | href | h4 | h8 | hremaining
  · left
    left
    exact hsolved
  · left
    right
    left
    exact hprod
  · left
    right
    right
    left
    exact hneg
  · left
    right
    right
    right
    left
    exact href
  · left
    right
    right
    right
    right
    left
    exact h4
  · left
    right
    right
    right
    right
    right
    exact h8
  · rcases hremaining with hC8 | hH2 | hE8 | hD4 | hQ8
    · obtain ⟨φ, ⟨e⟩, _, _, _, _, _, _, _, _, _⟩ := hC8
      rcases order72_e9_c8_branch_cases e with h0 | h1 | h2 | h3 | h4
      · left
        right
        left
        exact h0
      · left
        right
        right
        left
        exact h1
      · left
        right
        right
        right
        left
        exact h2
      · left
        right
        right
        right
        right
        left
        exact h3
      · left
        right
        right
        right
        right
        right
        exact h4
    · right
      left
      exact hH2
    · right
      right
      left
      exact hE8
    · right
      right
      right
      left
      exact hD4
    · right
      right
      right
      right
      exact hQ8

theorem order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_done
    {G : Type*} [Group G] :
    order72Sylow3NormalSemidirectCases G →
      order72Sylow3NormalPartialRepCasesC9AllE9C8Done G := by
  intro hcases
  exact order72PartialC9AllE9C8Done_of_odd_reps_done
    (order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_odd_reps_done hcases)

/-- The `n₃ = 1` branch with all `C9 ⋊ H` and `E9 ⋊ C8` cases reduced to explicit
representatives. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_done_of_sylow_three_normal
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : ∀ P : Sylow 3 G, (↑P : Subgroup G).Normal) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8Done G :=
  order72_sylow3_semidirect_cases_refined_c9_all_e9_c8_done
    (order72_semidirectProduct_standard_cases_of_sylow_three_normal hG hSyl)

/-- The `n₃ = 1` branch with all `C9 ⋊ H` and `E9 ⋊ C8` cases reduced to explicit
representatives. -/
theorem order72_partial_rep_cases_c9_all_e9_c8_done_of_card_sylow_three_eq_one
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72)
    (hSyl : Nat.card (Sylow 3 G) = 1) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8Done G := by
  exact order72_partial_rep_cases_c9_all_e9_c8_done_of_sylow_three_normal hG
    (fun P => sylow_three_normal_of_card_sylow_three_eq_one hSyl P)

/-- Current top-level reduction: in the Sylow-`3`-normal branch every `C9 ⋊ H` and
`E9 ⋊ C8` case is now explicit; the remaining semidirect action problems are
`E9 ⋊ H2`, `E9 ⋊ E8`, `E9 ⋊ D4` and `E9 ⋊ Q8`. -/
theorem order72_partial_classification_refined_c9_all_e9_c8_done
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalPartialRepCasesC9AllE9C8Done G ∨
      order72Sylow2NormalRepCases G ∨
      (Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) := by
  rcases order72_sylow_trichotomy hG with h3 | h2 | hres
  · exact Or.inl (order72_partial_rep_cases_c9_all_e9_c8_done_of_sylow_three_normal hG h3)
  · exact Or.inr (Or.inl (order72_classification_of_sylow_two_normal hG h2))
  · exact Or.inr (Or.inr hres)
end Smallgroups.UsefulTheorems
