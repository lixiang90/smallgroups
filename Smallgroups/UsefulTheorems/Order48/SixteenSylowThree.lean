/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.Sylow
import Smallgroups.UsefulTheorems.Order80.UniqueSylowFive
import Smallgroups.UsefulTheorems.SemidirectProductClassify
import Smallgroups.UsefulTheorems.Order80.SixteenSylowFive

/-!
# Groups of order 48 with sixteen Sylow-3 subgroups

This file handles the third branch of `order48_sylow_trichotomy`
(`Order48/Sylow.lean`): if a group `G` of order `48` has `n₃ = 16`, then its
Sylow `2`-subgroup `N` (of order `16`) is unique, hence normal, and
Schur–Zassenhaus splits `G` as `N ⋊[φ] C₃`.

The classification mirrors `Order80/SixteenSylowFive.lean` with `5 → 3`:

* the conjugation action of a generator of `C₃` on `N` is a **fixed-point-free**
  automorphism `σ` with `σ³ = 1` (`order48_sixteen_sylow_fpf`): a nontrivial
  fixed point would produce an involution `z` centralising the Sylow
  `3`-subgroup `Q = ⟨inr c⟩`; but `n₃ = 16` forces `N(Q) = Q` (order `3`),
  which cannot contain an involution;
* an order-`3` automorphism partitions any invariant subset into orbits of
  size `1` or `3` (`mulAut_three_card_modEq`, via
  `IsPGroup.card_modEq_card_fixedPoints`), so an invariant subset whose
  cardinality is not divisible by `3` contains a fixed point
  (`exists_fixed_of_three`);
* for `12` of the `14` isomorphism types of order-`16` groups there is a
  characteristic (hence `σ`-invariant) subset of cardinality not divisible by
  `3`, contradicting fixed-point-freeness (`no_fpf_of_pred_count`):
  - involutions (`x² = 1`, `x ≠ 1`): `C₁₆` (1), `SD₁₆` (5), `Q₁₆` (1),
    `C₄ × C₂²` (7), `D₈ × C₂` (11);
  - order-`8` elements (`x⁸ = 1`, `x⁴ ≠ 1`): `C₈ × C₂` (8), `M₁₆` (8),
    `D₁₆` (4);
  - nonidentity commutators (the commutator subgroup has order `2`):
    `(C₄ × C₂) ⋊ C₂`, `Q₈ ⋊ C₂`, `Q₈ × C₂`, `C₄ ⋊ C₄` (1 each);
* the survivors are `(C₂)⁴` and `C₄ × C₄`, and on each, all fixed-point-free
  order-`3` actions give isomorphic semidirect products:
  - `order48_c2pow4_unique`: fixed-point-freeness makes the `σ`-orbit of any
    `v ≠ 1` generate a `σ`-invariant subgroup `W` of order `≡ 1 (mod 3)`,
    i.e. `4`; picking `w ∉ W` gives a basis `v, σv, w, σw` on which `σ` acts
    as two copies of the companion matrix of `x² + x + 1` — a normal form
    independent of `φ`;
  - `order48_c4c4_unique`: the norm relation `σ²x · σx · x = 1` (the norm is a
    fixed point) shows `v, σv` generate unless `σ` preserves `⟨v⟩ ≅ C₄`, in
    which case the unique involution `v²` would be fixed; on the basis
    `v, σv` the action is the companion form `σ(v) = w`, `σ(w) = v⁻¹w⁻¹`.

Main results:

* `order48_semidirectProduct_of_sylow_three_sixteen` — the Schur–Zassenhaus
  reduction `G ≃* N ⋊[φ] C₃` with `|N| = 16`;
* `order48_c2pow4_unique`, `order48_c4c4_unique` — uniqueness over each
  surviving kernel;
* `order48_sixteen_sylow_classification` — **every** group of order `48` with
  `n₃ = 16` is isomorphic to `order48_c2pow4_semidirect_c3_rep` or to
  `order48_c4c4_semidirect_c3_rep`: there are exactly two such groups
  (`order48_two_reps_not_iso`);
* `order48_c2pow4_rep_card`, `order48_c2pow4_rep_sylow_three`,
  `order48_c4c4_rep_card`, `order48_c4c4_rep_sylow_three` — the
  representatives really are such groups: they have order `48` and `n₃ = 16`.
-/

namespace Smallgroups.UsefulTheorems

open Sylow

variable {G : Type*} [Group G]

/-! ### Homomorphisms out of `C₃` and `C₄` -/

/-- The generator of `C₃ = Multiplicative (ZMod 3)`. -/
private noncomputable abbrev c3gen : Multiplicative (ZMod 3) :=
  Multiplicative.ofAdd (1 : ZMod 3)

private theorem c3gen_pow_three : c3gen ^ 3 = 1 := by decide

private theorem c3gen_ne_one : c3gen ≠ 1 := by decide

private theorem c3gen_span (x : Multiplicative (ZMod 3)) :
    x = c3gen ^ (Multiplicative.toAdd x).val := by
  revert x; decide

/-- A hom out of `C₃` into any group, sending the generator to a chosen
order-dividing-`3` element. -/
noncomputable def C3_powHom {H : Type*} [Group H] (A : H) (hA : A ^ 3 = 1) :
    Multiplicative (ZMod 3) →* H :=
  MonoidHom.mk' (fun x => A ^ (Multiplicative.toAdd x).val) (by
    intro x y
    change A ^ (Multiplicative.toAdd (x * y)).val =
      A ^ (Multiplicative.toAdd x).val * A ^ (Multiplicative.toAdd y).val
    rw [← pow_add]
    have hval : (Multiplicative.toAdd (x * y)).val =
        ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) % 3 := by
      change (Multiplicative.toAdd x + Multiplicative.toAdd y).val = _
      rw [ZMod.val_add]
    rw [hval, ← Nat.div_add_mod ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) 3,
      pow_add, pow_mul, hA, one_pow, one_mul]
    congr 1
    omega)

theorem C3_powHom_gen {H : Type*} [Group H] (A : H) (hA : A ^ 3 = 1) :
    C3_powHom A hA c3gen = A := by
  change A ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3))).val = A
  norm_num [ZMod.val_one]

/-- A hom out of `C₄` into any group, sending the generator to a chosen
order-dividing-`4` element. -/
noncomputable def C4_powHom {H : Type*} [Group H] (A : H) (hA : A ^ 4 = 1) :
    Multiplicative (ZMod 4) →* H :=
  MonoidHom.mk' (fun x => A ^ (Multiplicative.toAdd x).val) (by
    intro x y
    change A ^ (Multiplicative.toAdd (x * y)).val =
      A ^ (Multiplicative.toAdd x).val * A ^ (Multiplicative.toAdd y).val
    rw [← pow_add]
    have hval : (Multiplicative.toAdd (x * y)).val =
        ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) % 4 := by
      change (Multiplicative.toAdd x + Multiplicative.toAdd y).val = _
      rw [ZMod.val_add]
    rw [hval, ← Nat.div_add_mod ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) 4,
      pow_add, pow_mul, hA, one_pow, one_mul]
    congr 1
    omega)

theorem C4_powHom_gen {H : Type*} [Group H] (A : H) (hA : A ^ 4 = 1) :
    C4_powHom A hA (Multiplicative.ofAdd (1 : ZMod 4)) = A := by
  change A ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 4))).val = A
  norm_num [ZMod.val_one]

/-- Homomorphisms out of `C₃` into any monoid are determined by the generator. -/
theorem c3_hom_ext {M : Type*} [Monoid M] {χ ψ : Multiplicative (ZMod 3) →* M}
    (h : χ c3gen = ψ c3gen) : χ = ψ := by
  apply MonoidHom.ext
  intro x
  rw [c3gen_span x, map_pow, map_pow, h]

/-! ### Orbit counting for an automorphism of order dividing `3`

An order-`3` permutation of a finite set has all orbits of size `1` or `3`, so
the total cardinality is congruent mod `3` to the number of fixed points.  We
derive it from `IsPGroup.card_modEq_card_fixedPoints` applied to the cyclic
subgroup generated by the permutation. -/

private theorem perm_three_card_modEq {α : Type*} [Finite α] (π : Equiv.Perm α)
    (h3 : ∀ y, π (π (π y)) = y) :
    Nat.card α ≡ Nat.card {y : α // π y = y} [MOD 3] := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpow : π ^ 3 = 1 := by
    have hπ3 : π ^ 3 = π * π * π := by
      rw [pow_succ, pow_succ, pow_one]
    ext y
    rw [hπ3]
    simpa [Equiv.Perm.mul_apply] using h3 y
  have hZ : IsPGroup 3 (Subgroup.zpowers π) := by
    rcases (Nat.dvd_prime (by norm_num)).mp (orderOf_dvd_of_pow_eq_one hpow) with h | h
    · exact IsPGroup.of_card (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (by rw [Nat.card_zpowers, h, pow_one])
  have hmod := hZ.card_modEq_card_fixedPoints α
  have hcardeq : Nat.card (MulAction.fixedPoints (Subgroup.zpowers π) α)
      = Nat.card {y : α // π y = y} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro y
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hy
      have := hy ⟨π, Subgroup.mem_zpowers π⟩
      rwa [Submonoid.mk_smul, Equiv.Perm.smul_def] at this
    · intro hy g
      have hle : Subgroup.zpowers π ≤ MulAction.stabilizer (Equiv.Perm α) y :=
        Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr
          (by rw [Equiv.Perm.smul_def]; exact hy))
      have := hle g.2
      rw [MulAction.mem_stabilizer_iff] at this
      exact this
  rw [hcardeq] at hmod
  exact hmod

/-- **Orbit counting on an invariant subset.** If `σ` is an automorphism with
`σ³ = 1` (pointwise) and `p` is a `σ`-invariant predicate, the number of
elements satisfying `p` is congruent mod `3` to the number of `σ`-fixed ones. -/
theorem mulAut_three_card_modEq {K : Type*} [Group K] [Finite K] (σ : MulAut K)
    (h3 : ∀ x, σ (σ (σ x)) = x) (p : K → Prop) (hp : ∀ x, p x → p (σ x)) :
    Nat.card {x : K // p x} ≡ Nat.card {x : K // p x ∧ σ x = x} [MOD 3] := by
  have hinj : Function.Injective
      (fun y : {x : K // p x} => (⟨σ y.1, hp y.1 y.2⟩ : {x : K // p x})) :=
    fun a b hab => Subtype.ext (σ.injective (congrArg Subtype.val hab))
  let π : Equiv.Perm {x : K // p x} :=
    Equiv.ofBijective _ ((Finite.injective_iff_bijective).mp hinj)
  have hπcoe : ∀ y : {x : K // p x}, (π y : K) = σ y.1 := fun y => rfl
  have h3' : ∀ y, π (π (π y)) = y := by
    intro y
    apply Subtype.ext
    rw [hπcoe, hπcoe, hπcoe]
    exact h3 y.1
  have hmod := perm_three_card_modEq π h3'
  have h2 : Nat.card {y : {x : K // p x} // π y = y} = Nat.card {x : K // p x ∧ σ x = x} := by
    apply Nat.card_congr
    refine ⟨fun y => ⟨y.1.1, y.1.2, ?_⟩, fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩, ?_, ?_⟩
    · have := congrArg Subtype.val y.2
      rwa [hπcoe] at this
    · exact Subtype.ext x.2.2
    · intro y; ext; rfl
    · intro x; rfl
  rw [h2] at hmod
  exact hmod

/-- If a `σ`-invariant predicate holds on a set of elements whose cardinality
is not divisible by `3`, then it holds at a `σ`-fixed element. -/
theorem exists_fixed_of_three {K : Type*} [Group K] [Finite K] (σ : MulAut K)
    (h3 : ∀ x, σ (σ (σ x)) = x) (p : K → Prop) (hp : ∀ x, p x → p (σ x))
    (hcard : ¬ (3 ∣ Nat.card {x : K // p x})) : ∃ x, p x ∧ σ x = x := by
  by_contra hcon
  haveI hempty : IsEmpty {x : K // p x ∧ σ x = x} := ⟨fun y => hcon ⟨y.1, y.2⟩⟩
  have h0 : Nat.card {x : K // p x ∧ σ x = x} = 0 := Nat.card_of_isEmpty
  have hmod := mulAut_three_card_modEq σ h3 p hp
  rw [h0] at hmod
  exact hcard (Nat.modEq_zero_iff_dvd.mp hmod)

/-- **No fixed-point-free automorphism of order dividing `3`** on a group with
a `σ`-invariant predicate, true only at nonidentity elements, whose cardinality
is not divisible by `3`. -/
theorem no_fpf_of_pred_count {K : Type*} [Group K] [Finite K] (σ : MulAut K)
    (h3 : ∀ x, σ (σ (σ x)) = x) (hfpf : ∀ x, σ x = x → x = 1)
    {p : K → Prop} (hp : ∀ x, p x → p (σ x)) (hp1 : ∀ x, p x → x ≠ 1)
    (hcard : ¬ (3 ∣ Nat.card {x : K // p x})) : False := by
  obtain ⟨x, hx, hfix⟩ := exists_fixed_of_three σ h3 p hp hcard
  exact hp1 x hx (hfpf x hfix)

/-- **No fixed-point-free automorphism of order dividing `3`** on a group where
the number of elements `x` with `x ^ m = 1` and `x ^ d ≠ 1` is not divisible by
`3`.  (Applied with `(m, d) = (2, 1)` — involutions — for `C₁₆`, `SD₁₆`,
`Q₁₆`, `C₄ × C₂²`, `D₈ × C₂`, and `(m, d) = (8, 4)` — order-`8` elements — for
`C₈ × C₂`, `M₁₆`, `D₁₆`.) -/
theorem no_fpf_of_pow_count_three {K : Type*} [Group K] [Finite K] (σ : MulAut K)
    (h3 : ∀ x, σ (σ (σ x)) = x) (hfpf : ∀ x, σ x = x → x = 1) (m d : ℕ)
    (hcard : ¬ (3 ∣ Nat.card {x : K // x ^ m = 1 ∧ x ^ d ≠ 1})) : False :=
  no_fpf_of_pred_count σ h3 hfpf
    (fun y hy => ⟨by rw [← map_pow, hy.1, map_one],
      fun h => hy.2 (σ.injective (by rw [← map_pow] at h; rw [h, map_one]))⟩)
    (fun y hy h1 => hy.2 (by rw [h1, one_pow])) hcard

/-- **No fixed-point-free automorphism of order dividing `3`** on a group where
the number of nonidentity commutators is not divisible by `3`.  (Applied to
`(C₄ × C₂) ⋊ C₂`, `Q₈ ⋊ C₂`, `Q₈ × C₂`, `C₄ ⋊ C₄`, each of which has a
commutator subgroup of order `2`, hence exactly one nonidentity commutator.) -/
theorem no_fpf_of_commutator_count {K : Type*} [Group K] [Finite K] (σ : MulAut K)
    (h3 : ∀ x, σ (σ (σ x)) = x) (hfpf : ∀ x, σ x = x → x = 1)
    (hcard : ¬ (3 ∣ Nat.card {x : K // (∃ a b : K, a * b * a⁻¹ * b⁻¹ = x) ∧ x ≠ 1})) :
    False :=
  no_fpf_of_pred_count σ h3 hfpf
    (fun y hy => by
      obtain ⟨a, b, hab⟩ := hy.1
      exact ⟨⟨σ a, σ b, by simp only [← hab, map_mul, map_inv]⟩,
        fun h => hy.2 (σ.injective (by rw [h, map_one]))⟩)
    (fun y hy => hy.2) hcard

/-! ### Applying a power of an automorphism -/

private theorem mulAut_pow_three_apply {K : Type*} [Group K] (f : MulAut K) (x : K) :
    (f ^ 3) x = f (f (f x)) := by
  have h : f ^ 3 = f * f * f := by
    rw [pow_succ, pow_succ, pow_one]
  rw [h]
  rfl

/-- The generator of `C₃` acts through `φ` by an automorphism of order
dividing `3` (pointwise form). -/
theorem actionC3_gen_three_apply {K : Type*} [Group K]
    (φ : Multiplicative (ZMod 3) →* MulAut K) (x : K) :
    φ c3gen (φ c3gen (φ c3gen x)) = x := by
  have hpow : φ c3gen ^ 3 = 1 := by rw [← map_pow, c3gen_pow_three, map_one]
  rw [← mulAut_pow_three_apply, hpow, MulAut.one_apply]

/-- Commuting `inr` past `inl` in a semidirect product. -/
private theorem inr_mul_inl {N G' : Type*} [Group N] [Group G'] {φ : G' →* MulAut N}
    (g : G') (n : N) :
    (SemidirectProduct.inr g : SemidirectProduct N G' φ) * SemidirectProduct.inl n =
      SemidirectProduct.inl (φ g n) * SemidirectProduct.inr g := by
  rw [SemidirectProduct.inl_aut, ← map_inv]
  group

/-! ### The Schur–Zassenhaus reduction: `G ≃* N ⋊[φ] K` with `|N| = 16`, `|K| = 3` -/

/-- **Semidirect-product reduction for order `48` with sixteen Sylow-`3`
subgroups.** If `G` has order `48` and `n₃ = 16`, its Sylow `2`-subgroup is
normal, and `G` is a semidirect product `N ⋊[φ] K` with `|N| = 16`, `|K| = 3`. -/
theorem order48_semidirectProduct_of_sylow_three_sixteen [Finite G] (hG : Nat.card G = 48)
    (hSyl : Nat.card (Sylow 3 G) = 16) :
    ∃ (N K : Subgroup G) (φ : K →* MulAut N),
      N.Normal ∧ Nat.card N = 16 ∧ Nat.card K = 3 ∧
        Nonempty (G ≃* SemidirectProduct N K φ) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 2 G))
  haveI hsub : Subsingleton (Sylow 2 G) :=
    (Nat.card_eq_one_iff_unique.mp
      (card_sylow_two_eq_one_of_card_sylow_three_eq_sixteen hG hSyl)).1
  haveI hnorm : (↑P0 : Subgroup G).Normal := Sylow.normal_of_subsingleton P0
  have hcardN : Nat.card (↑P0 : Subgroup G) = 16 := card_sylow_two_subgroup_of_card_48 hG P0
  have hidx : (↑P0 : Subgroup G).index = 3 := by
    have hmul := (↑P0 : Subgroup G).card_mul_index
    rw [hcardN, hG] at hmul
    omega
  have hcop : Nat.Coprime (Nat.card (↑P0 : Subgroup G)) (↑P0 : Subgroup G).index := by
    rw [hcardN, hidx]
    norm_num
  obtain ⟨K, φ, ⟨e⟩⟩ := schurZassenhaus_semidirectProduct (↑P0 : Subgroup G) hcop
  have hcardK : Nat.card K = 3 := by
    have h1 : Nat.card G = Nat.card (↑P0 : Subgroup G) * Nat.card K := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
    rw [hG, hcardN] at h1
    omega
  exact ⟨↑P0, K, φ, hnorm, hcardN, hcardK, ⟨e⟩⟩

/-! ### Fixed-point-freeness from `n₃ = 16`

In `H = K ⋊[φ] C₃` with `n₃ = 16`, the Sylow-`3` subgroup `Q = ⟨inr c⟩` is
self-normalising (`|N(Q)| = 48 / 16 = 3`).  A nontrivial `φ(c)`-fixed point
`x ∈ K` yields an involution `z ∈ ⟨x⟩` with `inl z` centralising, hence
normalising, `Q` — an involution in a group of order `3`, contradiction. -/

theorem order48_sixteen_sylow_fpf {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 16)
    (φ : Multiplicative (ZMod 3) →* MulAut K)
    (hSyl : Nat.card (Sylow 3 (SemidirectProduct K (Multiplicative (ZMod 3)) φ)) = 16) :
    ∀ x : K, φ c3gen x = x → x = 1 := by
  intro x hx
  by_contra hne
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set H := SemidirectProduct K (Multiplicative (ZMod 3)) φ with hH
  haveI : Finite H := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hcardH : Nat.card H = 48 := by
    rw [hH, SemidirectProduct.card, hK, Nat.card_eq_fintype_card]
    decide
  -- an involution z in ⟨x⟩ fixed by φ(c)
  have hdvd : orderOf x ∣ 16 := hK ▸ orderOf_dvd_natCard x
  have hdvd16 : orderOf x ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
    exact hdvd
  obtain ⟨i, hile, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd16
  have hipos : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h1
    · exfalso; apply hne; rw [← orderOf_eq_one_iff, hord, h0, pow_zero]
    · exact h1
  set z := x ^ (2 ^ (i - 1)) with hz
  have hz2 : z * z = 1 := by
    rw [hz, ← pow_add, ← two_mul, ← pow_succ']
    have : i - 1 + 1 = i := by omega
    rw [this, ← hord]
    exact pow_orderOf_eq_one x
  have hz1 : z ≠ 1 := by
    intro h
    have hdvd2 : orderOf x ∣ 2 ^ (i - 1) := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd2
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd2
    omega
  have hzfix : φ c3gen z = z := by rw [hz, map_pow, hx]
  -- inl z commutes with inr c
  have haut := SemidirectProduct.inl_aut (φ := φ) c3gen z
  rw [hzfix, map_inv] at haut
  have hcomm1 : (SemidirectProduct.inl z : H) * SemidirectProduct.inr c3gen
      = SemidirectProduct.inr c3gen * SemidirectProduct.inl z := by
    conv_lhs => rw [haut]
    exact inv_mul_cancel_right _ _
  -- the Sylow-3 subgroup ⟨inr c⟩ and its normaliser
  have horder : orderOf (SemidirectProduct.inr c3gen : H) = 3 := by
    rw [orderOf_injective (SemidirectProduct.inr (φ := φ)) SemidirectProduct.inr_injective]
    exact orderOf_eq_prime c3gen_pow_three c3gen_ne_one
  have hzpcard : Nat.card (Subgroup.zpowers (SemidirectProduct.inr c3gen : H)) = 3 := by
    rw [Nat.card_zpowers, horder]
  have hzp : IsPGroup 3 (Subgroup.zpowers (SemidirectProduct.inr c3gen : H)) :=
    IsPGroup.of_card (by rw [hzpcard, pow_one])
  obtain ⟨Q, hle⟩ := hzp.exists_le_sylow
  have hQ3 : Nat.card (↑Q : Subgroup H) = 3 := card_sylow_three_subgroup_of_card_48 hcardH Q
  have heqzp : Subgroup.zpowers (SemidirectProduct.inr c3gen : H) = ↑Q :=
    eq_of_le_of_card_eq hle (by rw [hzpcard, hQ3])
  haveI : Finite (Sylow 3 H) := Nat.finite_of_card_ne_zero (by rw [hSyl]; norm_num)
  have hidx : (Subgroup.normalizer (Q : Set H)).index = 16 := by
    rw [← Q.card_eq_index_normalizer]
    exact hSyl
  have hNcard : Nat.card (Subgroup.normalizer (Q : Set H)) = 3 := by
    have hmul := Subgroup.card_mul_index (Subgroup.normalizer (Q : Set H))
    rw [hidx, hcardH] at hmul
    omega
  have heqQN : (↑Q : Subgroup H) = Subgroup.normalizer (Q : Set H) := by
    apply eq_of_le_of_card_eq
    · rw [← Sylow.coe_coe]
      exact Subgroup.le_normalizer
    · rw [hQ3, hNcard]
  -- inl z normalises Q
  have hmemN : SemidirectProduct.inl z ∈ Subgroup.normalizer (Q : Set H) := by
    rw [← Sylow.coe_coe, ← heqzp, Subgroup.mem_normalizer_iff]
    intro h
    have hcz : Commute (SemidirectProduct.inl z : H) (SemidirectProduct.inr c3gen) := hcomm1
    constructor
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [← hk, (hcz.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hh2 : h = (SemidirectProduct.inr c3gen : H) ^ k := by
        have h1 : (SemidirectProduct.inl z : H)⁻¹ *
            ((SemidirectProduct.inr c3gen : H) ^ k) * SemidirectProduct.inl z = h := by
          rw [hk]; group
        rw [← h1, ((hcz.zpow_right k).inv_left).eq, mul_assoc, inv_mul_cancel, mul_one]
      rw [hh2]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  -- hence inl z ∈ Q = ⟨inr c⟩, so z = 1: contradiction
  have hzQ : SemidirectProduct.inl z ∈ Subgroup.zpowers (SemidirectProduct.inr c3gen : H) := by
    rw [heqzp, heqQN]
    exact hmemN
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzQ
  have hleft := congrArg SemidirectProduct.left hk
  rw [← map_zpow, SemidirectProduct.left_inr, SemidirectProduct.left_inl] at hleft
  exact hz1 hleft.symm

/-! ### The elementary abelian kernel `(C₂)⁴`: generators and the companion normal form -/

/-- The four coordinate generators of `(C₂)⁴`. -/
private noncomputable def Lg1 : order16_wild_C2pow4 := (Multiplicative.ofAdd 1, 1, 1, 1)
private noncomputable def Lg2 : order16_wild_C2pow4 := (1, Multiplicative.ofAdd 1, 1, 1)
private noncomputable def Lg3 : order16_wild_C2pow4 := (1, 1, Multiplicative.ofAdd 1, 1)
private noncomputable def Lg4 : order16_wild_C2pow4 := (1, 1, 1, Multiplicative.ofAdd 1)

private theorem Lg1_ne_one : Lg1 ≠ 1 := by decide

private theorem c2pow4_pow_two (x : order16_wild_C2pow4) : x ^ 2 = 1 := by revert x; decide

private theorem c2pow4_mul_self (x : order16_wild_C2pow4) : x * x = 1 := by revert x; decide

/-- Homomorphisms out of `(C₂)⁴` into any monoid are determined by the four
coordinate generators. -/
theorem c2pow4_hom_ext {M : Type*} [Monoid M] {f g : order16_wild_C2pow4 →* M}
    (h1 : f Lg1 = g Lg1) (h2 : f Lg2 = g Lg2)
    (h3 : f Lg3 = g Lg3) (h4 : f Lg4 = g Lg4) : f = g := by
  apply MonoidHom.ext
  intro x
  have hx : x = Lg1 ^ (Multiplicative.toAdd x.1).val *
      (Lg2 ^ (Multiplicative.toAdd x.2.1).val *
        (Lg3 ^ (Multiplicative.toAdd x.2.2.1).val *
          Lg4 ^ (Multiplicative.toAdd x.2.2.2).val)) := by
    revert x; decide
  rw [hx]
  simp only [map_mul, map_pow, h1, h2, h3, h4]

private theorem C2_powHom_gen {H : Type*} [Group H] (B : H) (hB : B ^ 2 = 1) :
    C2_powHom B hB (Multiplicative.ofAdd (1 : ZMod 2)) = B := by
  change B ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = B
  norm_num [ZMod.val_one]

/-- The homomorphism `(C₂)⁴ →* (C₂)⁴` determined by images `w₁, w₂, w₃, w₄` of
the four coordinate generators. -/
private noncomputable def c2pow4_basisHom (w1 w2 w3 w4 : order16_wild_C2pow4) :
    order16_wild_C2pow4 →* order16_wild_C2pow4 :=
  (C2_powHom w1 (c2pow4_pow_two w1)).coprod ((C2_powHom w2 (c2pow4_pow_two w2)).coprod
    ((C2_powHom w3 (c2pow4_pow_two w3)).coprod (C2_powHom w4 (c2pow4_pow_two w4))))

private theorem c2pow4_basisHom_g1 (w1 w2 w3 w4 : order16_wild_C2pow4) :
    c2pow4_basisHom w1 w2 w3 w4 Lg1 = w1 := by
  simp [c2pow4_basisHom, Lg1, MonoidHom.coprod_apply, C2_powHom_gen, map_one]

private theorem c2pow4_basisHom_g2 (w1 w2 w3 w4 : order16_wild_C2pow4) :
    c2pow4_basisHom w1 w2 w3 w4 Lg2 = w2 := by
  simp [c2pow4_basisHom, Lg2, MonoidHom.coprod_apply, C2_powHom_gen, map_one]

private theorem c2pow4_basisHom_g3 (w1 w2 w3 w4 : order16_wild_C2pow4) :
    c2pow4_basisHom w1 w2 w3 w4 Lg3 = w3 := by
  simp [c2pow4_basisHom, Lg3, MonoidHom.coprod_apply, C2_powHom_gen, map_one]

private theorem c2pow4_basisHom_g4 (w1 w2 w3 w4 : order16_wild_C2pow4) :
    c2pow4_basisHom w1 w2 w3 w4 Lg4 = w4 := by
  simp [c2pow4_basisHom, Lg4, MonoidHom.coprod_apply, C2_powHom_gen, map_one]

/-- The companion automorphism `σ₀` of `x² + x + 1` on each of two blocks of
`(C₂)⁴`: `e₁ ↦ e₂ ↦ e₁e₂` and `e₃ ↦ e₄ ↦ e₃e₄`. -/
noncomputable def order48_c2pow4_sigma0 : order16_wild_C2pow4 ≃* order16_wild_C2pow4 where
  toFun p := (p.2.1, p.1 * p.2.1, p.2.2.2, p.2.2.1 * p.2.2.2)
  invFun q := (q.1 * q.2.1, q.1, q.2.2.1 * q.2.2.2, q.2.2.1)
  left_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  right_inv := by rintro ⟨a, b, c, d⟩; ext <;> revert a b c d <;> decide
  map_mul' := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩; ext <;> revert a b c d a' b' c' d' <;> decide

private theorem sigma0_c2_three (p : order16_wild_C2pow4) :
    order48_c2pow4_sigma0 (order48_c2pow4_sigma0 (order48_c2pow4_sigma0 p)) = p := by
  revert p; decide

private theorem sigma0_c2_g1 : order48_c2pow4_sigma0 Lg1 = Lg2 := by decide
private theorem sigma0_c2_g2 : order48_c2pow4_sigma0 Lg2 = Lg1 * Lg2 := by decide
private theorem sigma0_c2_g3 : order48_c2pow4_sigma0 Lg3 = Lg4 := by decide
private theorem sigma0_c2_g4 : order48_c2pow4_sigma0 Lg4 = Lg3 * Lg4 := by decide

private theorem sigma0_c2_cube :
    (order48_c2pow4_sigma0 : MulAut order16_wild_C2pow4) ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  rw [mulAut_pow_three_apply]
  exact sigma0_c2_three x

private theorem sigma0_c2_fpf : ∀ x : order16_wild_C2pow4,
    order48_c2pow4_sigma0 x = x → x = 1 := by
  decide

/-- The reference action `φ₀ : C₃ →* Aut (C₂)⁴`, sending the generator to the
companion automorphism `σ₀`. -/
noncomputable def order48_c2pow4_phi0 :
    Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4 :=
  C3_powHom (order48_c2pow4_sigma0 : MulAut order16_wild_C2pow4) sigma0_c2_cube

theorem order48_c2pow4_phi0_gen :
    order48_c2pow4_phi0 c3gen = (order48_c2pow4_sigma0 : MulAut order16_wild_C2pow4) :=
  C3_powHom_gen _ _

/-- **A group of order `48` with `n₃ = 16`:** `(C₂)⁴ ⋊[φ₀] C₃`. -/
noncomputable abbrev order48_c2pow4_semidirect_c3_rep : Type :=
  SemidirectProduct order16_wild_C2pow4 (Multiplicative (ZMod 3)) order48_c2pow4_phi0

/-! ### The kernel `C₄ × C₄`: generators and the companion normal form -/

/-- The kernel `C₄ × C₄`. -/
abbrev order48_C4C4 : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

/-- The two coordinate generators of `C₄ × C₄`. -/
private noncomputable def Gc1 : order48_C4C4 := (Multiplicative.ofAdd 1, 1)
private noncomputable def Gc2 : order48_C4C4 := (1, Multiplicative.ofAdd 1)

private theorem Gc1_pow4 : Gc1 ^ 4 = 1 := by decide

private theorem Gc1_sq_ne_one : Gc1 ^ 2 ≠ 1 := by decide

private theorem Gc1_ne_one : Gc1 ≠ 1 := by decide

private theorem Gc1_orderOf : orderOf Gc1 = 4 := by
  have hdvd : orderOf Gc1 ∣ 4 := orderOf_dvd_of_pow_eq_one Gc1_pow4
  have hne1 : orderOf Gc1 ≠ 1 := by
    rw [orderOf_eq_one_iff]
    exact Gc1_ne_one
  have hne2 : orderOf Gc1 ≠ 2 := fun h =>
    Gc1_sq_ne_one (orderOf_dvd_iff_pow_eq_one.mp (h ▸ dvd_refl 2))
  have hmem : orderOf Gc1 ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact absurd h hne1
  · exact absurd h hne2
  · exact h

/-- Homomorphisms out of `C₄ × C₄` into any monoid are determined by the two
coordinate generators. -/
theorem c4c4_hom_ext {M : Type*} [Monoid M] {f g : order48_C4C4 →* M}
    (h1 : f Gc1 = g Gc1) (h2 : f Gc2 = g Gc2) : f = g := by
  apply MonoidHom.ext
  intro x
  have hx : x = Gc1 ^ (Multiplicative.toAdd x.1).val *
      Gc2 ^ (Multiplicative.toAdd x.2).val := by
    revert x; decide
  rw [hx]
  simp only [map_mul, map_pow, h1, h2]

/-- The homomorphism `C₄ × C₄ →* C₄ × C₄` determined by images `v, w` of the
two coordinate generators. -/
private noncomputable def c4c4_basisHom (v w : order48_C4C4) (hv : v ^ 4 = 1)
    (hw : w ^ 4 = 1) : order48_C4C4 →* order48_C4C4 :=
  (C4_powHom v hv).coprod (C4_powHom w hw)

private theorem c4c4_basisHom_g1 (v w : order48_C4C4) (hv hw) :
    c4c4_basisHom v w hv hw Gc1 = v := by
  simp [c4c4_basisHom, Gc1, MonoidHom.coprod_apply, C4_powHom_gen, map_one]

private theorem c4c4_basisHom_g2 (v w : order48_C4C4) (hv hw) :
    c4c4_basisHom v w hv hw Gc2 = w := by
  simp [c4c4_basisHom, Gc2, MonoidHom.coprod_apply, C4_powHom_gen, map_one]

/-- The companion automorphism `σ₀` on `C₄ × C₄`: `e₁ ↦ e₂ ↦ e₁⁻¹e₂⁻¹`. -/
noncomputable def order48_c4c4_sigma0 : order48_C4C4 ≃* order48_C4C4 where
  toFun p := (p.2⁻¹, p.1 * p.2⁻¹)
  invFun q := (q.1⁻¹ * q.2, q.1⁻¹)
  left_inv := by rintro ⟨x, y⟩; ext <;> revert x y <;> decide
  right_inv := by rintro ⟨x, y⟩; ext <;> revert x y <;> decide
  map_mul' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩; ext <;> revert x y x' y' <;> decide

private theorem sigma0_c4_three (p : order48_C4C4) :
    order48_c4c4_sigma0 (order48_c4c4_sigma0 (order48_c4c4_sigma0 p)) = p := by
  revert p; decide

private theorem sigma0_c4_g1 : order48_c4c4_sigma0 Gc1 = Gc2 := by decide
private theorem sigma0_c4_g2 : order48_c4c4_sigma0 Gc2 = Gc1⁻¹ * Gc2⁻¹ := by decide

private theorem sigma0_c4_cube :
    (order48_c4c4_sigma0 : MulAut order48_C4C4) ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  rw [mulAut_pow_three_apply]
  exact sigma0_c4_three x

private theorem sigma0_c4_fpf : ∀ x : order48_C4C4,
    order48_c4c4_sigma0 x = x → x = 1 := by
  decide

/-- The reference action `φ₀ : C₃ →* Aut (C₄ × C₄)`. -/
noncomputable def order48_c4c4_phi0 :
    Multiplicative (ZMod 3) →* MulAut order48_C4C4 :=
  C3_powHom (order48_c4c4_sigma0 : MulAut order48_C4C4) sigma0_c4_cube

theorem order48_c4c4_phi0_gen :
    order48_c4c4_phi0 c3gen = (order48_c4c4_sigma0 : MulAut order48_C4C4) :=
  C3_powHom_gen _ _

/-- **A group of order `48` with `n₃ = 16`:** `(C₄ × C₄) ⋊[φ₀] C₃`. -/
noncomputable abbrev order48_c4c4_semidirect_c3_rep : Type :=
  SemidirectProduct order48_C4C4 (Multiplicative (ZMod 3)) order48_c4c4_phi0

/-! ### Uniqueness over `(C₂)⁴` -/

/-- **Uniqueness of the fixed-point-free semidirect product `(C₂)⁴ ⋊ C₃`.**
Every action `φ : C₃ →* Aut (C₂)⁴` whose generator acts fixed-point-freely
gives a semidirect product isomorphic to the reference one.  The orbit
`v, σv` of any `v ≠ 1` spans a `σ`-invariant subgroup `W` of order
`≡ 1 (mod 3)` and `≤ 4`, hence exactly `4`; picking `w ∉ W`, the basis
`v, σv, w, σw` conjugates `σ` to two copies of the companion matrix of
`x² + x + 1`. -/
theorem order48_c2pow4_unique
    (φ : Multiplicative (ZMod 3) →* MulAut order16_wild_C2pow4)
    (hfpf : ∀ x : order16_wild_C2pow4, φ c3gen x = x → x = 1) :
    Nonempty (SemidirectProduct order16_wild_C2pow4 (Multiplicative (ZMod 3)) φ ≃*
      order48_c2pow4_semidirect_c3_rep) := by
  set σ : MulAut order16_wild_C2pow4 := φ c3gen with hσdef
  have h3σ : ∀ x, σ (σ (σ x)) = x := actionC3_gen_three_apply φ
  have hK0card : Nat.card order16_wild_C2pow4 = 16 := by
    rw [Nat.card_eq_fintype_card]; decide
  -- the norm relation: `x · σx · σ²x` is fixed, hence trivial
  have hnorm : ∀ x : order16_wild_C2pow4, x * σ x * σ (σ x) = 1 := by
    intro x
    apply hfpf
    rw [map_mul, map_mul, h3σ x, mul_comm (σ x * σ (σ x)) x, ← mul_assoc]
  have hσ2 : ∀ x : order16_wild_C2pow4, σ (σ x) = σ x * x := by
    intro x
    have h : (x * σ x) * σ (σ x) = 1 := hnorm x
    have h2 : σ (σ x) = (x * σ x)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_left (c2pow4_mul_self (σ x)),
      inv_eq_of_mul_eq_one_left (c2pow4_mul_self x)]
  -- a nontrivial element and its orbit subgroup
  obtain ⟨v, hv1⟩ := exists_ne (1 : order16_wild_C2pow4)
  set W : Subgroup order16_wild_C2pow4 := Subgroup.closure {v, σ v} with hWdef
  have hvW : v ∈ W := Subgroup.subset_closure (Set.mem_insert v _)
  have hσvW : σ v ∈ W :=
    Subgroup.subset_closure (Set.mem_insert_of_mem v (Set.mem_singleton _))
  have hWinv : ∀ x, x ∈ W → σ x ∈ W := by
    have hle : W ≤ W.comap
        (σ : order16_wild_C2pow4 ≃* order16_wild_C2pow4).toMonoidHom := by
      rw [hWdef, Subgroup.closure_le]
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact Subgroup.mem_comap.mpr hσvW
      · exact Subgroup.mem_comap.mpr (by rw [hσ2 v]; exact W.mul_mem hσvW hvW)
    intro x hx
    exact Subgroup.mem_comap.mp (hle hx)
  have hWfix : Nat.card {x : order16_wild_C2pow4 // x ∈ W ∧ σ x = x} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · constructor
      rintro ⟨a, haW, hafix⟩ ⟨b, hbW, hbfix⟩
      have ha := hfpf a hafix
      have hb := hfpf b hbfix
      subst ha
      subst hb
      rfl
    · exact ⟨⟨1, W.one_mem, map_one σ⟩⟩
  have hWmod := mulAut_three_card_modEq σ h3σ (· ∈ W) hWinv
  rw [hWfix] at hWmod
  have hWdvd : Nat.card {x : order16_wild_C2pow4 // x ∈ W} ∣ 16 := by
    rw [← hK0card]
    exact Subgroup.card_subgroup_dvd_card W
  -- `|W| ≤ 4`: `W` is contained in the range of a hom out of `C₂ × C₂`
  have hv2 : v ^ 2 = 1 := c2pow4_pow_two v
  have hσv2 : (σ v) ^ 2 = 1 := c2pow4_pow_two _
  set T0 := (C2_powHom v hv2).coprod (C2_powHom (σ v) hσv2) with hT0def
  have hWle : W ≤ T0.range := by
    rw [hWdef, Subgroup.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · refine ⟨(Multiplicative.ofAdd 1, 1), ?_⟩
      simp [hT0def, MonoidHom.coprod_apply, C2_powHom_gen]
    · refine ⟨(1, Multiplicative.ofAdd 1), ?_⟩
      simp [hT0def, MonoidHom.coprod_apply, C2_powHom_gen]
  have hT0card : Nat.card T0.range ≤ 4 := by
    have h1 : Nat.card (Set.range (fun x => T0 x)) ≤
        Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
      Nat.card_range_le _
    have h2 : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
      rw [Nat.card_eq_fintype_card]; decide
    have h3 : Nat.card T0.range = Nat.card (Set.range (fun x => T0 x)) := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun x => by rw [MonoidHom.mem_range, Set.mem_range])
    rw [h3, ← h2]
    exact h1
  have hWcard : Nat.card {x : order16_wild_C2pow4 // x ∈ W} = 4 := by
    have hdvd' : Nat.card {x : order16_wild_C2pow4 // x ∈ W} ∣ Nat.card T0.range :=
      Subgroup.card_dvd_of_le hWle
    have hle4 : Nat.card {x : order16_wild_C2pow4 // x ∈ W} ≤ 4 :=
      (Nat.le_of_dvd Nat.card_pos hdvd').trans hT0card
    have hdne1 : Nat.card {x : order16_wild_C2pow4 // x ∈ W} ≠ 1 := by
      intro h1
      have hbot : W = ⊥ := Subgroup.card_eq_one.mp h1
      rw [hbot] at hvW
      exact hv1 (Subgroup.mem_bot.mp hvW)
    have hdmod : Nat.card {x : order16_wild_C2pow4 // x ∈ W} % 3 = 1 := by
      unfold Nat.ModEq at hWmod; omega
    have hdpos : 0 < Nat.card {x : order16_wild_C2pow4 // x ∈ W} := Nat.card_pos
    set d := Nat.card {x : order16_wild_C2pow4 // x ∈ W} with hddef
    interval_cases d <;> omega
  -- an element outside `W`
  have hw_exists : ∃ w : order16_wild_C2pow4, w ∉ W := by
    by_contra hall
    push_neg at hall
    have htop : W = ⊤ := Subgroup.eq_top_iff'.mpr hall
    have h16 : Nat.card {x : order16_wild_C2pow4 // x ∈ W} = 16 := by
      have h1 : Nat.card {x : order16_wild_C2pow4 // x ∈ W} =
          Nat.card order16_wild_C2pow4 :=
        Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => htop ▸ Subgroup.mem_top x))
      rw [h1, hK0card]
    omega
  obtain ⟨w, hwW⟩ := hw_exists
  -- the basis-change homomorphism
  set T : order16_wild_C2pow4 →* order16_wild_C2pow4 :=
    c2pow4_basisHom v (σ v) w (σ w) with hTdef
  -- the intertwining relation `σ ∘ T = T ∘ σ₀`
  have hcommHom : (σ : order16_wild_C2pow4 ≃* order16_wild_C2pow4).toMonoidHom.comp T
      = T.comp (order48_c2pow4_sigma0 :
          order16_wild_C2pow4 ≃* order16_wild_C2pow4).toMonoidHom := by
    apply c2pow4_hom_ext
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sigma0_c2_g1, hTdef,
        c2pow4_basisHom_g1, c2pow4_basisHom_g2]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sigma0_c2_g2, hTdef,
        map_mul, c2pow4_basisHom_g1, c2pow4_basisHom_g2]
      rw [hσ2 v, mul_comm]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sigma0_c2_g3, hTdef,
        c2pow4_basisHom_g3, c2pow4_basisHom_g4]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sigma0_c2_g4, hTdef,
        map_mul, c2pow4_basisHom_g3, c2pow4_basisHom_g4]
      rw [hσ2 w, mul_comm]
  have hpt : ∀ y, σ (T y) = T (order48_c2pow4_sigma0 y) := by
    intro y
    have := DFunLike.congr_fun hcommHom y
    simpa using this
  -- the range of `T` is `σ`-invariant, hence has order `≡ 1 (mod 3)`
  have hUinv : ∀ x, x ∈ T.range → σ x ∈ T.range := by
    rintro x ⟨y, rfl⟩
    exact ⟨order48_c2pow4_sigma0 y, hpt y⟩
  have hUfix : Nat.card {x : order16_wild_C2pow4 // x ∈ T.range ∧ σ x = x} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · constructor
      rintro ⟨a, haW, hafix⟩ ⟨b, hbW, hbfix⟩
      have ha := hfpf a hafix
      have hb := hfpf b hbfix
      subst ha
      subst hb
      rfl
    · exact ⟨⟨1, T.range.one_mem, map_one σ⟩⟩
  have hUmod := mulAut_three_card_modEq σ h3σ (· ∈ T.range) hUinv
  rw [hUfix] at hUmod
  have hWleU : W ≤ T.range := by
    rw [hWdef, Subgroup.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ⟨Lg1, c2pow4_basisHom_g1 _ _ _ _⟩
    · exact ⟨Lg2, c2pow4_basisHom_g2 _ _ _ _⟩
  have hwU : w ∈ T.range := ⟨Lg3, c2pow4_basisHom_g3 _ _ _ _⟩
  have hUcard : Nat.card {x : order16_wild_C2pow4 // x ∈ T.range} = 16 := by
    have hUdvd : Nat.card {x : order16_wild_C2pow4 // x ∈ T.range} ∣ 16 := by
      rw [← hK0card]
      exact Subgroup.card_subgroup_dvd_card T.range
    have h4dvd : 4 ∣ Nat.card {x : order16_wild_C2pow4 // x ∈ T.range} := by
      have h1 := Subgroup.card_dvd_of_le hWleU
      rwa [hWcard] at h1
    have hdne4 : Nat.card {x : order16_wild_C2pow4 // x ∈ T.range} ≠ 4 := by
      intro h4
      have heq : W = T.range := eq_of_le_of_card_eq hWleU (by rw [hWcard, h4])
      rw [heq] at hwU
      exact hwW hwU
    have hdmod : Nat.card {x : order16_wild_C2pow4 // x ∈ T.range} % 3 = 1 := by
      unfold Nat.ModEq at hUmod; omega
    have hdpos : 0 < Nat.card {x : order16_wild_C2pow4 // x ∈ T.range} := Nat.card_pos
    have hdle : Nat.card {x : order16_wild_C2pow4 // x ∈ T.range} ≤ 16 :=
      Nat.le_of_dvd (by norm_num) hUdvd
    set d := Nat.card {x : order16_wild_C2pow4 // x ∈ T.range} with hddef
    interval_cases d <;> omega
  have hUtop : T.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hUcard, hK0card])
  have hTsurj : Function.Surjective T := MonoidHom.range_eq_top.mp hUtop
  have hTbij : Function.Bijective T :=
    ⟨(Finite.injective_iff_surjective).mpr hTsurj, hTsurj⟩
  set τ : order16_wild_C2pow4 ≃* order16_wild_C2pow4 :=
    MulEquiv.ofBijective T hTbij with hτdef
  -- conjugating `φ₀` by `τ` gives `φ`
  have hact : (MulAut.conj (τ : MulAut order16_wild_C2pow4)).toMonoidHom.comp
      order48_c2pow4_phi0 = φ := by
    apply c3_hom_ext
    change MulAut.conj (τ : MulAut order16_wild_C2pow4) (order48_c2pow4_phi0 c3gen) = φ c3gen
    rw [order48_c2pow4_phi0_gen, ← hσdef, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    apply MulEquiv.ext
    intro y
    rw [MulAut.mul_apply, MulAut.mul_apply]
    exact (hpt y).symm
  exact ⟨(semidirectProductCongr_eq hact.symm).trans
    (semidirectProductCongrConj (τ : MulAut order16_wild_C2pow4)).symm⟩

/-! ### Uniqueness over `C₄ × C₄` -/

/-- **Uniqueness of the fixed-point-free semidirect product `(C₄ × C₄) ⋊ C₃`.**
Every action `φ : C₃ →* Aut (C₄ × C₄)` whose generator acts fixed-point-freely
gives a semidirect product isomorphic to the reference one.  The norm
`σ²x · σx · x` is a fixed point, hence trivial, so `σ` has companion form
`σ(w) = v⁻¹w⁻¹` on any pair `v, σv`; these generate `C₄ × C₄` unless `σ`
preserves `⟨v⟩`, in which case the unique involution `v² ∈ ⟨v⟩` would be a
nontrivial fixed point. -/
theorem order48_c4c4_unique
    (φ : Multiplicative (ZMod 3) →* MulAut order48_C4C4)
    (hfpf : ∀ x : order48_C4C4, φ c3gen x = x → x = 1) :
    Nonempty (SemidirectProduct order48_C4C4 (Multiplicative (ZMod 3)) φ ≃*
      order48_c4c4_semidirect_c3_rep) := by
  set σ : MulAut order48_C4C4 := φ c3gen with hσdef
  have h3σ : ∀ x, σ (σ (σ x)) = x := actionC3_gen_three_apply φ
  have hKcard : Nat.card order48_C4C4 = 16 := by
    rw [Nat.card_eq_fintype_card]; decide
  -- the norm relation: `σ²x · σx · x` is fixed, hence trivial
  have hnorm : ∀ x : order48_C4C4, σ (σ x) * σ x * x = 1 := by
    intro x
    apply hfpf
    rw [map_mul, map_mul, h3σ x, mul_assoc, mul_comm x (σ (σ x) * σ x)]
  have hsq2 : ∀ x : order48_C4C4, σ (σ x) = (σ x)⁻¹ * x⁻¹ := by
    intro x
    have h : σ (σ x) * (σ x * x) = 1 := by
      rw [← mul_assoc]
      exact hnorm x
    rw [eq_inv_of_mul_eq_one_right h, mul_inv_rev, mul_comm x⁻¹ (σ x)⁻¹]
  -- the orbit subgroup of the generator `Gc1`
  set W : Subgroup order48_C4C4 := Subgroup.closure {Gc1, σ Gc1} with hWdef
  have hvW : Gc1 ∈ W := Subgroup.subset_closure (Set.mem_insert Gc1 _)
  have hσvW : σ Gc1 ∈ W :=
    Subgroup.subset_closure (Set.mem_insert_of_mem Gc1 (Set.mem_singleton _))
  have hWinv : ∀ x, x ∈ W → σ x ∈ W := by
    have hle : W ≤ W.comap (σ : order48_C4C4 ≃* order48_C4C4).toMonoidHom := by
      rw [hWdef, Subgroup.closure_le]
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact Subgroup.mem_comap.mpr hσvW
      · exact Subgroup.mem_comap.mpr (by
          rw [hsq2 Gc1]
          exact W.mul_mem (W.inv_mem hσvW) (W.inv_mem hvW))
    intro x hx
    exact Subgroup.mem_comap.mp (hle hx)
  have hWfix : Nat.card {x : order48_C4C4 // x ∈ W ∧ σ x = x} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · constructor
      rintro ⟨a, haW, hafix⟩ ⟨b, hbW, hbfix⟩
      have ha := hfpf a hafix
      have hb := hfpf b hbfix
      subst ha
      subst hb
      rfl
    · exact ⟨⟨1, W.one_mem, map_one σ⟩⟩
  have hWmod := mulAut_three_card_modEq σ h3σ (· ∈ W) hWinv
  rw [hWfix] at hWmod
  have hWdvd : Nat.card {x : order48_C4C4 // x ∈ W} ∣ 16 := by
    rw [← hKcard]
    exact Subgroup.card_subgroup_dvd_card W
  have h4dvdW : 4 ∣ Nat.card {x : order48_C4C4 // x ∈ W} := by
    have h1 := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hvW)
    rwa [Nat.card_zpowers, Gc1_orderOf] at h1
  -- `|W| ≠ 4`: otherwise `W = ⟨Gc1⟩` and the unique involution `Gc1²` is fixed
  have hWne4 : Nat.card {x : order48_C4C4 // x ∈ W} ≠ 4 := by
    intro h4
    have hzle : Subgroup.zpowers Gc1 ≤ W := Subgroup.zpowers_le.mpr hvW
    have hzcard : Nat.card (Subgroup.zpowers Gc1) = 4 := by
      rw [Nat.card_zpowers, Gc1_orderOf]
    have heq : Subgroup.zpowers Gc1 = W := eq_of_le_of_card_eq hzle (by rw [hzcard, h4])
    have hv2W : Gc1 ^ 2 ∈ W := W.pow_mem hvW 2
    have hσv2W : σ (Gc1 ^ 2) ∈ W := hWinv _ hv2W
    rw [← heq] at hσv2W
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hσv2W
    have hsq : (σ (Gc1 ^ 2)) ^ 2 = 1 := by
      have h1 : (Gc1 ^ 2) ^ 2 = Gc1 ^ 4 := by rw [← pow_mul]
      rw [← map_pow, h1, Gc1_pow4, map_one]
    have hne : σ (Gc1 ^ 2) ≠ 1 := by
      intro h
      exact Gc1_sq_ne_one (σ.injective (by rw [h, map_one]))
    -- reduce the exponent `j` mod `4`
    have hjsq : Gc1 ^ (j * 2) = 1 := by
      have h1 : (Gc1 ^ j) ^ 2 = 1 := by rw [← hj]; exact hsq
      rw [← zpow_natCast, ← zpow_mul] at h1
      exact h1
    have hdvd4 : (4 : ℤ) ∣ j * 2 := by
      have h1 := orderOf_dvd_iff_zpow_eq_one.mp hjsq
      rwa [Gc1_orderOf] at h1
    obtain ⟨m, hm⟩ : (2 : ℤ) ∣ j := by omega
    have hjm : Gc1 ^ j = (Gc1 ^ 2) ^ m := by rw [hm, ← zpow_mul]
    rw [hjm] at hj
    have hv2z : (Gc1 ^ 2 : order48_C4C4) ^ (2 : ℤ) = 1 := by
      rw [← zpow_natCast, ← pow_mul, Gc1_pow4]
    -- `(Gc1²)^m` is a fixed point squared to `1`, so it is `1` or `Gc1²`
    have hcontra : (Gc1 ^ 2) ^ m = Gc1 ^ 2 := by
      rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
      · exfalso
        apply hne
        rw [hj, hk, show (k + k : ℤ) = 2 * k by ring, zpow_mul, hv2z, one_zpow]
      · rw [hk, zpow_add, zpow_mul, hv2z, one_zpow, one_mul, zpow_one]
    exact Gc1_sq_ne_one (hfpf _ (hj.trans hcontra))
  have hWcard : Nat.card {x : order48_C4C4 // x ∈ W} = 16 := by
    have hdmod : Nat.card {x : order48_C4C4 // x ∈ W} % 3 = 1 := by
      unfold Nat.ModEq at hWmod; omega
    have hdpos : 0 < Nat.card {x : order48_C4C4 // x ∈ W} := Nat.card_pos
    have hdle : Nat.card {x : order48_C4C4 // x ∈ W} ≤ 16 :=
      Nat.le_of_dvd (by norm_num) hWdvd
    set d := Nat.card {x : order48_C4C4 // x ∈ W} with hddef
    interval_cases d <;> omega
  have hWtop : W = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hWcard, hKcard])
  -- the basis-change homomorphism
  have hσv4 : (σ Gc1) ^ 4 = 1 := by rw [← map_pow, Gc1_pow4, map_one]
  set T : order48_C4C4 →* order48_C4C4 :=
    c4c4_basisHom Gc1 (σ Gc1) Gc1_pow4 hσv4 with hTdef
  have hTrange : T.range = ⊤ := by
    rw [eq_top_iff, ← hWtop, hWdef, Subgroup.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ⟨Gc1, c4c4_basisHom_g1 _ _ _ _⟩
    · exact ⟨Gc2, c4c4_basisHom_g2 _ _ _ _⟩
  have hTsurj : Function.Surjective T := MonoidHom.range_eq_top.mp hTrange
  have hTbij : Function.Bijective T :=
    ⟨(Finite.injective_iff_surjective).mpr hTsurj, hTsurj⟩
  set τ : order48_C4C4 ≃* order48_C4C4 := MulEquiv.ofBijective T hTbij with hτdef
  -- the intertwining relation `σ ∘ T = T ∘ σ₀`
  have hcommHom : (σ : order48_C4C4 ≃* order48_C4C4).toMonoidHom.comp T
      = T.comp (order48_c4c4_sigma0 : order48_C4C4 ≃* order48_C4C4).toMonoidHom := by
    apply c4c4_hom_ext
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sigma0_c4_g1, hTdef,
        c4c4_basisHom_g1, c4c4_basisHom_g2]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sigma0_c4_g2, hTdef,
        map_mul, map_inv, c4c4_basisHom_g1, c4c4_basisHom_g2]
      rw [hsq2 Gc1, mul_comm]
  have hpt : ∀ y, σ (T y) = T (order48_c4c4_sigma0 y) := by
    intro y
    have := DFunLike.congr_fun hcommHom y
    simpa using this
  -- conjugating `φ₀` by `τ` gives `φ`
  have hact : (MulAut.conj (τ : MulAut order48_C4C4)).toMonoidHom.comp
      order48_c4c4_phi0 = φ := by
    apply c3_hom_ext
    change MulAut.conj (τ : MulAut order48_C4C4) (order48_c4c4_phi0 c3gen) = φ c3gen
    rw [order48_c4c4_phi0_gen, ← hσdef, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    apply MulEquiv.ext
    intro y
    rw [MulAut.mul_apply, MulAut.mul_apply]
    exact (hpt y).symm
  exact ⟨(semidirectProductCongr_eq hact.symm).trans
    (semidirectProductCongrConj (τ : MulAut order48_C4C4)).symm⟩

/-! ### The representatives really have `n₃ = 16` -/

/-- Conjugating the standard Sylow-`3` generator `inr c` by an arbitrary
element of the reference semidirect product. -/
private theorem rep_conj_inr_gen {K : Type*} [Group K] (σ₀ : MulAut K) (hσ₀3 : σ₀ ^ 3 = 1)
    (h : SemidirectProduct K (Multiplicative (ZMod 3)) (C3_powHom σ₀ hσ₀3)) :
    h * SemidirectProduct.inr c3gen * h⁻¹ =
      SemidirectProduct.inl (h.left * σ₀ h.left⁻¹) * SemidirectProduct.inr c3gen := by
  have hφ : C3_powHom σ₀ hσ₀3 c3gen = σ₀ := C3_powHom_gen _ _
  have step2 : SemidirectProduct.inr h.right * SemidirectProduct.inr c3gen *
      SemidirectProduct.inr h.right⁻¹ = SemidirectProduct.inr c3gen := by
    rw [← map_mul, ← map_mul]
    congr 1
    rw [mul_left_comm, mul_inv_cancel_right]
  rw [← SemidirectProduct.inl_left_mul_inr_right h, mul_inv, ← map_inv, ← map_inv]
  calc SemidirectProduct.inl h.left * SemidirectProduct.inr h.right * SemidirectProduct.inr c3gen
        * (SemidirectProduct.inr h.right⁻¹ * SemidirectProduct.inl h.left⁻¹)
      = SemidirectProduct.inl h.left * (SemidirectProduct.inr h.right *
          SemidirectProduct.inr c3gen * SemidirectProduct.inr h.right⁻¹) *
          SemidirectProduct.inl h.left⁻¹ := by group
    _ = SemidirectProduct.inl h.left * SemidirectProduct.inr c3gen *
          SemidirectProduct.inl h.left⁻¹ := by rw [step2]
    _ = SemidirectProduct.inl h.left * (SemidirectProduct.inl (C3_powHom σ₀ hσ₀3 c3gen h.left⁻¹) *
          SemidirectProduct.inr c3gen) := by rw [mul_assoc, inr_mul_inl]
    _ = SemidirectProduct.inl (h.left * σ₀ h.left⁻¹) * SemidirectProduct.inr c3gen := by
        rw [← mul_assoc, ← map_mul, hφ]

/-- **The reference semidirect products have sixteen Sylow-`3` subgroups.** If
`σ₀` is a fixed-point-free automorphism of order dividing `3` of a group `K`
of order `16`, then in `K ⋊ C₃` the Sylow-`3` subgroup `⟨inr c⟩` is
self-normalising: conjugating `inr c` by `h` has `N`-component
`h.left · (σ₀ h.left)⁻¹`, which is `1` only when `h.left` is fixed, i.e.
trivial.  Hence `N(Q) = Q` has index `16`. -/
theorem order48_sylow_three_rep_of_fpf {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 16)
    (σ₀ : MulAut K) (hσ₀3 : σ₀ ^ 3 = 1) (hfpf0 : ∀ x : K, σ₀ x = x → x = 1) :
    Nat.card (Sylow 3 (SemidirectProduct K (Multiplicative (ZMod 3)) (C3_powHom σ₀ hσ₀3)))
      = 16 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set H := SemidirectProduct K (Multiplicative (ZMod 3)) (C3_powHom σ₀ hσ₀3) with hH
  haveI : Finite H := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hcardH : Nat.card H = 48 := by
    rw [hH, SemidirectProduct.card, hK, Nat.card_eq_fintype_card]
    decide
  set c : H := SemidirectProduct.inr c3gen with hc
  have horder : orderOf c = 3 := by
    rw [hc, orderOf_injective (SemidirectProduct.inr (φ := C3_powHom σ₀ hσ₀3))
      SemidirectProduct.inr_injective]
    exact orderOf_eq_prime c3gen_pow_three c3gen_ne_one
  have hzpcard : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, horder]
  have hzp : IsPGroup 3 (Subgroup.zpowers c) := IsPGroup.of_card (by rw [hzpcard, pow_one])
  obtain ⟨Q, hle⟩ := hzp.exists_le_sylow
  have hQ3 : Nat.card (↑Q : Subgroup H) = 3 := card_sylow_three_subgroup_of_card_48 hcardH Q
  have heqzp : Subgroup.zpowers c = ↑Q := eq_of_le_of_card_eq hle (by rw [hzpcard, hQ3])
  have hnormQ : Subgroup.normalizer (Q : Set H) = ↑Q := by
    apply le_antisymm
    · intro h hh
      rw [Subgroup.mem_normalizer_iff] at hh
      have hcQ : c ∈ (↑Q : Set H) := by
        rw [← heqzp]
        exact Subgroup.mem_zpowers c
      have hch := (hh c).mp hcQ
      rw [← heqzp] at hch
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hch
      rw [hc, rep_conj_inr_gen σ₀ hσ₀3 h, ← map_zpow] at hj
      have hleft : h.left * σ₀ h.left⁻¹ = 1 := by
        have h2 := congrArg SemidirectProduct.left hj
        simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
          SemidirectProduct.left_inr, SemidirectProduct.right_inl, map_one, MulAut.one_apply,
          mul_one] at h2
        exact h2.symm
      have hfix : σ₀ h.left⁻¹ = h.left⁻¹ := eq_inv_of_mul_eq_one_left hleft
      have hl1 : h.left = 1 := by
        have h1 := hfpf0 h.left⁻¹ hfix
        rwa [inv_eq_one] at h1
      have h3' : h = SemidirectProduct.inr h.right := by
        rw [← SemidirectProduct.inl_left_mul_inr_right h, hl1, map_one, one_mul]
      rw [h3', ← heqzp]
      refine Subgroup.mem_zpowers_iff.mpr ⟨((Multiplicative.toAdd h.right).val : ℤ), ?_⟩
      rw [← map_zpow, zpow_natCast, ← c3gen_span h.right]
    · rw [← Sylow.coe_coe]
      exact Subgroup.le_normalizer
  have hNcard : Nat.card (Subgroup.normalizer (Q : Set H)) = 3 := by rw [hnormQ]; exact hQ3
  have hidx : (Subgroup.normalizer (Q : Set H)).index = 16 := by
    have hmul := Subgroup.card_mul_index (Subgroup.normalizer (Q : Set H))
    rw [hNcard, hcardH] at hmul
    omega
  haveI : Finite (Sylow 3 H) := Sylow.finite_of_finiteIndex Q
  rw [← Q.card_eq_index_normalizer]
  exact hidx

theorem order48_c2pow4_rep_card : Nat.card order48_c2pow4_semidirect_c3_rep = 48 := by
  change Nat.card (SemidirectProduct _ _ _) = 48
  rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

/-- `(C₂)⁴ ⋊[φ₀] C₃` has sixteen Sylow-`3` subgroups. -/
theorem order48_c2pow4_rep_sylow_three :
    Nat.card (Sylow 3 order48_c2pow4_semidirect_c3_rep) = 16 :=
  order48_sylow_three_rep_of_fpf (by rw [Nat.card_eq_fintype_card]; decide)
    _ sigma0_c2_cube sigma0_c2_fpf

theorem order48_c4c4_rep_card : Nat.card order48_c4c4_semidirect_c3_rep = 48 := by
  change Nat.card (SemidirectProduct _ _ _) = 48
  rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

/-- `(C₄ × C₄) ⋊[φ₀] C₃` has sixteen Sylow-`3` subgroups. -/
theorem order48_c4c4_rep_sylow_three :
    Nat.card (Sylow 3 order48_c4c4_semidirect_c3_rep) = 16 :=
  order48_sylow_three_rep_of_fpf (by rw [Nat.card_eq_fintype_card]; decide)
    _ sigma0_c4_cube sigma0_c4_fpf

/-! ### The classification: exactly two groups of order `48` with `n₃ = 16` -/

/-- **Classification of groups of order `48` with sixteen Sylow-`3`
subgroups.** Any such group is isomorphic to `(C₂)⁴ ⋊[φ₀] C₃` or to
`(C₄ × C₄) ⋊[φ₀] C₃`. -/
theorem order48_sixteen_sylow_classification [Finite G] (hG : Nat.card G = 48)
    (hSyl : Nat.card (Sylow 3 G) = 16) :
    Nonempty (G ≃* order48_c2pow4_semidirect_c3_rep) ∨
      Nonempty (G ≃* order48_c4c4_semidirect_c3_rep) := by
  obtain ⟨N, K, φ, _, hcardN, hcardK, ⟨e⟩⟩ :=
    order48_semidirectProduct_of_sylow_three_sixteen hG hSyl
  obtain ⟨eK⟩ := prime_classification (p := 3) (by norm_num) hcardK
  obtain ⟨i, ⟨eN⟩⟩ := order16_wild_classification (G := N) hcardN
  -- the transported Sylow-3 count and fixed-point-freeness, for each branch
  fin_cases i
  -- i = 0 : (C₂)⁴ — the first surviving case
  · obtain ⟨eC⟩ := order16_A5_iso_concrete
    have e' := e.trans (SemidirectProduct.congr' (eN.trans eC) eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_C2pow4)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact Or.inl ⟨e'.trans (order48_c2pow4_unique _ hfpf).some⟩
  -- i = 1 : C₈ × C₂ — 8 elements of order 8
  · have e' := e.trans (SemidirectProduct.congr' eN eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_G1)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_pow_count_three _ (actionC3_gen_three_apply _) hfpf 8 4
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 2 : SD₁₆ — 5 involutions
  · have e' := e.trans (SemidirectProduct.congr' eN eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_G2)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_pow_count_three _ (actionC3_gen_three_apply _) hfpf 2 1
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 3 : M₁₆ — 8 elements of order 8
  · have e' := e.trans (SemidirectProduct.congr' eN eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_G3)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_pow_count_three _ (actionC3_gen_three_apply _) hfpf 8 4
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 4 : D₁₆ — 4 elements of order 8
  · have e' := e.trans (SemidirectProduct.congr' eN eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_G4)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_pow_count_three _ (actionC3_gen_three_apply _) hfpf 8 4
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 5 : Q₁₆ — 1 involution
  · have e' := e.trans (SemidirectProduct.congr' eN eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_G5)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_pow_count_three _ (actionC3_gen_three_apply _) hfpf 2 1
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 6 : C₁₆ — 1 involution
  · obtain ⟨eC⟩ := order16_A1_iso_concrete
    have e' := e.trans (SemidirectProduct.congr' (eN.trans eC) eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := Multiplicative (ZMod 16))
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_pow_count_three _ (actionC3_gen_three_apply _) hfpf 2 1
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 7 : C₄ × C₂ × C₂ — 7 involutions
  · have e' := e.trans (SemidirectProduct.congr' eN eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_G7)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_pow_count_three _ (actionC3_gen_three_apply _) hfpf 2 1
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 8 : D₈ × C₂ — 11 involutions
  · have e' := e.trans (SemidirectProduct.congr' eN eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_G8)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_pow_count_three _ (actionC3_gen_three_apply _) hfpf 2 1
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 9 : (C₄ × C₂) ⋊ C₂ — 1 nonidentity commutator
  · have e' := e.trans (SemidirectProduct.congr' eN eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_G9)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_commutator_count _ (actionC3_gen_three_apply _) hfpf
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 10 : Q₈ ⋊ C₂ — 1 nonidentity commutator
  · have e' := e.trans (SemidirectProduct.congr' eN eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_G10)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_commutator_count _ (actionC3_gen_three_apply _) hfpf
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 11 : Q₈ × C₂ — 1 nonidentity commutator
  · have e' := e.trans (SemidirectProduct.congr' eN eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_G11)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_commutator_count _ (actionC3_gen_three_apply _) hfpf
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 12 : C₄ ⋊ C₄ — 1 nonidentity commutator
  · have e' := e.trans (SemidirectProduct.congr' eN eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order16_wild_G12)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact (no_fpf_of_commutator_count _ (actionC3_gen_three_apply _) hfpf
      (by rw [Nat.card_eq_fintype_card]; decide)).elim
  -- i = 13 : C₄ × C₄ — the second surviving case
  · obtain ⟨eC⟩ := order16_A3_iso_concrete
    have e' := e.trans (SemidirectProduct.congr' (eN.trans eC) eK)
    have hSyl' := (card_sylow_of_mulEquiv 3 e').symm.trans hSyl
    have hfpf := order48_sixteen_sylow_fpf (K := order48_C4C4)
      (by rw [Nat.card_eq_fintype_card]; decide) _ hSyl'
    exact Or.inr ⟨e'.trans (order48_c4c4_unique _ hfpf).some⟩

/-- **The two representatives are not isomorphic**: an isomorphism would
restrict to `(C₂)⁴ ≃* C₄ × C₄`, but the latter has an element of order `4`
and the former does not. -/
theorem order48_two_reps_not_iso :
    ¬ Nonempty (order48_c2pow4_semidirect_c3_rep ≃* order48_c4c4_semidirect_c3_rep) := by
  rintro ⟨e⟩
  obtain ⟨eN⟩ := semidirectProduct_congr_domain (φ1 := order48_c2pow4_phi0)
    (φ2 := order48_c4c4_phi0)
    (by rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide)
    (by rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide) e
  have h1 : orderOf (eN.symm Gc1) = 4 := by
    rw [orderOf_injective eN.symm.toMonoidHom eN.symm.injective]
    exact Gc1_orderOf
  have h2 : (eN.symm Gc1) ^ 2 = 1 := c2pow4_pow_two _
  have hdvd : orderOf (eN.symm Gc1) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [h1] at hdvd
  norm_num at hdvd

end Smallgroups.UsefulTheorems
