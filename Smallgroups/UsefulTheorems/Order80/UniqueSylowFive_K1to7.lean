/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order80.UniqueSylowFive

/-!
# Isomorphism classes of `C₅ ⋊ Kᵢ` for `i = 1, …, 7`

`UniqueSylowFive.lean` shows that if `G` has order `80` with a unique Sylow-`5` subgroup, then
`G ≅ SemidirectProduct C₅ K φ` for one of the `14` isomorphism types `K = K₀, …, K₁₃` of order
`16`, and (via `order80_classify_Kᵢ`) narrows `φ = unitAutHom.comp χ` to a finite list of
candidate characters `χ : Kᵢ →* (ZMod 5)ˣ`.

Different `χ`'s in that list can still give *isomorphic* semidirect products: since `N = C₅` has
order coprime to `Nat.card Kᵢ`, `N` is characteristic in every such semidirect product
(`characteristic_of_coprime_index`), so by `semidirectProduct_congr_range` two candidates
`χ, χ'` give isomorphic groups **iff** they lie in the same orbit of `Aut(Kᵢ)` acting on
`Hom(Kᵢ, (ZMod 5)ˣ)` by precomposition (composing the action with `θ ∈ Aut(C₅)` contributes
nothing extra, since `Aut(C₅) ≅ (ZMod 5)ˣ` is abelian, so conjugation by `θ` on `MulAut C₅` is
trivial). This file works out that orbit structure for `K₁ = C₈ × C₂` and `K₂ = SD₁₆`.
-/

namespace Smallgroups.UsefulTheorems

/-! ## General orbit-merging tool -/

/-- **Precomposing a character with a `K`-automorphism gives an isomorphic semidirect product.**
If `χ' = χ ∘ σ` for `σ ∈ Aut K`, then `C₅ ⋊[χ] K ≅ C₅ ⋊[χ'] K`. This is the tool that merges
`Aut(K)`-orbit-equivalent candidates from `order80_classify_Kᵢ` into a single isomorphism class. -/
theorem semidirectProduct_of_comp_eq {K : Type*} [Group K] {χ χ' : K →* (ZMod 5)ˣ} (σ : K ≃* K)
    (hχ : χ.comp σ.toMonoidHom = χ') :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ) ≃*
      SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ')) := by
  have h : (unitAutHom.comp χ).comp σ.toMonoidHom = unitAutHom.comp χ' := by
    rw [MonoidHom.comp_assoc, hχ]
  exact ⟨(semidirectProductCongrAut σ).symm.trans (semidirectProductCongr_eq h)⟩

/-! ## General distinctness tool: kernel-element-order invariant

To show two representative characters `χ, χ' : K →* (ZMod 5)ˣ` give **non-isomorphic**
semidirect products `C₅ ⋊[χ] K`, `C₅ ⋊[χ'] K`, it suffices to exhibit `d` with `¬ 5 ∣ d` that
occurs as the order of some element of `ker χ` but no element of `ker χ'`: the generator of the
`C₅`-factor commutes with `x` iff `x`'s `K`-component lies in the kernel of the action
(`order80_inl_gen_commute_iff`), and this data transports along any isomorphism. -/

theorem c5_hom_ext {M : Type*} [Monoid M] {χ ψ : Multiplicative (ZMod 5) →* M}
    (h : χ (Multiplicative.ofAdd (1 : ZMod 5)) = ψ (Multiplicative.ofAdd (1 : ZMod 5))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  let n : ZMod 5 := Multiplicative.toAdd x
  have hx : x = (Multiplicative.ofAdd (1 : ZMod 5)) ^ n.val := by
    rw [show x = Multiplicative.ofAdd n from (ofAdd_toAdd _).symm]
    calc
      Multiplicative.ofAdd n = Multiplicative.ofAdd ((n.val : ZMod 5)) := by
        rw [ZMod.natCast_zmod_val]
      _ = Multiplicative.ofAdd (n.val • (1 : ZMod 5)) := by simp
      _ = (Multiplicative.ofAdd (1 : ZMod 5)) ^ n.val := by rw [ofAdd_nsmul]
  rw [hx, map_pow, map_pow, h]

/-- The only automorphism of `C₅` fixing a generator is the identity. -/
theorem order80_mulAut_c5_fixing_gen_eq_one (σ : MulAut (Multiplicative (ZMod 5)))
    (h : σ (Multiplicative.ofAdd (1 : ZMod 5)) = Multiplicative.ofAdd (1 : ZMod 5)) : σ = 1 := by
  have heq : σ.toMonoidHom = (1 : MulAut (Multiplicative (ZMod 5))).toMonoidHom :=
    c5_hom_ext (by simpa using h)
  ext x
  exact DFunLike.congr_fun heq x

theorem pow_five_eq_one_c5 (x : Multiplicative (ZMod 5)) : x ^ 5 = 1 := by revert x; decide

/-- Any element of order `5` (i.e. the full group order) generates `C₅`. -/
theorem c5_zpowers_eq_top_of_orderOf_eq_five {n : Multiplicative (ZMod 5)} (hn : orderOf n = 5) :
    Subgroup.zpowers n = ⊤ := by
  have hFcard : Fintype.card (Multiplicative (ZMod 5)) = 5 := by simp
  have hcard : Nat.card (Subgroup.zpowers n) = Nat.card (Multiplicative (ZMod 5)) := by
    rw [Nat.card_zpowers, hn, Nat.card_eq_fintype_card, hFcard]
  have hGcard : Nat.card (Multiplicative (ZMod 5)) = 5 := by
    rw [Nat.card_eq_fintype_card, hFcard]
  have hmulindex := (Subgroup.zpowers n).card_mul_index
  rw [hcard, hGcard] at hmulindex
  have hindex1 : (Subgroup.zpowers n).index = 1 :=
    Nat.eq_of_mul_eq_mul_left (show 0 < 5 by norm_num) (by rw [hmulindex, mul_one])
  exact Subgroup.index_eq_one.mp hindex1

/-- Any automorphism of `C₅` fixing an order-`5` element (equivalently, any generator) is the
identity. -/
theorem order80_mulAut_c5_fixing_ord5_eq_one {n : Multiplicative (ZMod 5)} (hn : orderOf n = 5)
    (σ : MulAut (Multiplicative (ZMod 5))) (h : σ n = n) : σ = 1 := by
  have htop := c5_zpowers_eq_top_of_orderOf_eq_five hn
  have hmem : Multiplicative.ofAdd (1 : ZMod 5) ∈ Subgroup.zpowers n := htop ▸ Subgroup.mem_top _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  apply order80_mulAut_c5_fixing_gen_eq_one
  rw [← hj, map_zpow, h]

/-- An order-`5` element's `inl`-image commutes with `x` iff `x`'s `K`-component acts trivially
under `φ`. -/
theorem order80_inl_gen_commute_iff {K : Type*} [Group K]
    {φ : K →* MulAut (Multiplicative (ZMod 5))} {n0 : Multiplicative (ZMod 5)}
    (hn0 : orderOf n0 = 5) (x : SemidirectProduct (Multiplicative (ZMod 5)) K φ) :
    Commute (SemidirectProduct.inl n0 : SemidirectProduct (Multiplicative (ZMod 5)) K φ) x ↔
      φ (SemidirectProduct.rightHom x) = 1 := by
  constructor
  · intro hc
    apply order80_mulAut_c5_fixing_ord5_eq_one hn0
    have hleft := congrArg SemidirectProduct.left hc
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply] at hleft
    have h3 : x.left * n0 = x.left * φ x.right n0 := by rw [mul_comm]; exact hleft
    exact (mul_left_cancel h3).symm
  · intro hφ
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, MulAut.one_apply,
        SemidirectProduct.rightHom_eq_right] at hφ ⊢
      rw [hφ, MulAut.one_apply, mul_comm]
    · simp

/-- If `k ∈ ker χ`, `inl a` commutes with `inr k` for every `a` (no generator needed). -/
theorem order80_inl_inr_commute_of_ker {K : Type*} [Group K]
    {φ : K →* MulAut (Multiplicative (ZMod 5))} {k : K} (hk : φ k = 1)
    (a : Multiplicative (ZMod 5)) :
    Commute (SemidirectProduct.inl a : SemidirectProduct (Multiplicative (ZMod 5)) K φ)
      (SemidirectProduct.inr k) := by
  apply SemidirectProduct.ext
  · simp [hk]
  · simp

/-- Any order-`5` element of `C₅ ⋊[φ'] K` (`K` finite of order coprime to `5`) lies in the
`C₅`-factor. -/
theorem order80_ord5_elt_eq_inl {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 5 (Fintype.card K)) {φ' : K →* MulAut (Multiplicative (ZMod 5))}
    {x' : SemidirectProduct (Multiplicative (ZMod 5)) K φ'} (hx'ord : orderOf x' = 5) :
    ∃ n' : Multiplicative (ZMod 5), x' = SemidirectProduct.inl n' ∧ orderOf n' = 5 := by
  have hdvd1 : orderOf (SemidirectProduct.rightHom x') ∣ 5 := by
    have := orderOf_map_dvd SemidirectProduct.rightHom x'
    rwa [hx'ord] at this
  have hdvd2 : orderOf (SemidirectProduct.rightHom x') ∣ Fintype.card K := orderOf_dvd_card
  have hgcd : orderOf (SemidirectProduct.rightHom x') ∣ Nat.gcd 5 (Fintype.card K) :=
    Nat.dvd_gcd hdvd1 hdvd2
  rw [hK] at hgcd
  have hrx' : SemidirectProduct.rightHom x' = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hx'eq : x' = SemidirectProduct.inl x'.left := by
    apply SemidirectProduct.ext
    · simp
    · simpa [SemidirectProduct.rightHom_eq_right] using hrx'
  refine ⟨x'.left, hx'eq, ?_⟩
  have hthis := hx'ord
  rw [hx'eq, orderOf_injective _ SemidirectProduct.inl_injective] at hthis
  exact hthis

/-- If an element `x` of `C₅ ⋊[χ] K` commutes with the (order-`5`) `C₅`-generator and has order
`d` (not a multiple of `5`), then `x` lies in `K` (`x.left = 1`) and `x.right ∈ ker χ` has order
`d` too. -/
theorem order80_centralizer_elt_decomp {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 5 (Fintype.card K)) {χ : K →* (ZMod 5)ˣ}
    {n0 : Multiplicative (ZMod 5)} (hn0 : orderOf n0 = 5) {d : ℕ} (hd : ¬ (5 ∣ d))
    {x : SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ)}
    (hx : Commute (SemidirectProduct.inl n0) x) (hxord : orderOf x = d) :
    x.left = 1 ∧ χ (SemidirectProduct.rightHom x) = 1 ∧
      orderOf (SemidirectProduct.rightHom x) = d := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmem : χ (SemidirectProduct.rightHom x) = 1 := by
    have := (order80_inl_gen_commute_iff hn0 x).mp hx
    rwa [MonoidHom.comp_apply, ← MonoidHom.map_one unitAutHom,
      Function.Injective.eq_iff (unitAutHom_injective (p := 5))] at this
  have hcommuteNK : Commute (SemidirectProduct.inl x.left :
      SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ))
      (SemidirectProduct.inr (SemidirectProduct.rightHom x)) :=
    order80_inl_inr_commute_of_ker (by rw [MonoidHom.comp_apply, hmem, map_one]) _
  have hxdecomp : x = SemidirectProduct.inl x.left *
      SemidirectProduct.inr (SemidirectProduct.rightHom x) := by
    rw [SemidirectProduct.rightHom_eq_right, SemidirectProduct.inl_left_mul_inr_right]
  have hxleftord : orderOf x.left ∣ 5 := orderOf_dvd_of_pow_eq_one (pow_five_eq_one_c5 _)
  have hxrightord2 : orderOf (SemidirectProduct.rightHom x) ∣ Fintype.card K := orderOf_dvd_card
  have hxrightcop : Nat.gcd 5 (orderOf (SemidirectProduct.rightHom x)) = 1 := by
    have hstep : Nat.gcd 5 (orderOf (SemidirectProduct.rightHom x)) ∣ Nat.gcd 5 (Fintype.card K) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans hxrightord2)
    rw [hK] at hstep
    exact Nat.dvd_one.mp hstep
  have hcop : Nat.Coprime (orderOf x.left) (orderOf (SemidirectProduct.rightHom x)) := by
    rcases (Nat.dvd_prime (by norm_num)).mp hxleftord with h1' | h1'
    · rw [h1']; exact Nat.coprime_one_left _
    · rw [h1']; exact hxrightcop
  have hordmul : orderOf x = orderOf x.left * orderOf (SemidirectProduct.rightHom x) := by
    conv_lhs => rw [hxdecomp]
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcommuteNK
      (by rw [orderOf_injective _ SemidirectProduct.inl_injective,
        orderOf_injective _ SemidirectProduct.inr_injective]; exact hcop)]
    rw [orderOf_injective _ SemidirectProduct.inl_injective,
      orderOf_injective _ SemidirectProduct.inr_injective]
  rw [hxord] at hordmul
  have hxleft1 : x.left = 1 := by
    rcases (Nat.dvd_prime (by norm_num)).mp hxleftord with h1' | h1'
    · exact orderOf_eq_one_iff.mp h1'
    · exfalso
      apply hd
      rw [hordmul, h1']
      exact ⟨_, rfl⟩
  refine ⟨hxleft1, hmem, ?_⟩
  rw [hxleft1, orderOf_one, one_mul] at hordmul
  exact hordmul.symm

/-- **Kernel-element-order invariant for distinguishing semidirect products.** If some element
of `ker χ` has order `d` (not a multiple of `5`) but no element of `ker χ'` does, then
`C₅ ⋊[χ] K` and `C₅ ⋊[χ'] K` are not isomorphic. -/
theorem order80_ne_of_ker_order {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 5 (Fintype.card K)) {χ χ' : K →* (ZMod 5)ˣ} {d : ℕ} (hd : ¬ (5 ∣ d))
    (h1 : ∃ k : K, χ k = 1 ∧ orderOf k = d)
    (h2 : ∀ k : K, χ' k = 1 → orderOf k ≠ d) :
    IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ) ≃*
      SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ')) := by
  constructor
  intro e
  obtain ⟨k, hk1, hkd⟩ := h1
  set n0 : Multiplicative (ZMod 5) := Multiplicative.ofAdd (1 : ZMod 5) with hn0
  have hn0ord : orderOf n0 = 5 := by
    rw [hn0, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hφk1 : (unitAutHom.comp χ) k = 1 := by rw [MonoidHom.comp_apply, hk1, map_one]
  have hcommute : Commute
      (SemidirectProduct.inl n0 : SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ))
      (SemidirectProduct.inr k) := by
    rw [order80_inl_gen_commute_iff hn0ord]
    simpa using hφk1
  have hyorder : orderOf (SemidirectProduct.inr k :
      SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ)) = d := by
    rw [orderOf_injective _ SemidirectProduct.inr_injective]; exact hkd
  have hcommute' := hcommute.map e
  have hyorder' : orderOf (e (SemidirectProduct.inr k)) = d := by
    rw [MulEquiv.orderOf_eq]; exact hyorder
  obtain ⟨n', hx'eq, hn'ord⟩ := order80_ord5_elt_eq_inl hK
    (show orderOf (e (SemidirectProduct.inl n0)) = 5 by
      rw [MulEquiv.orderOf_eq, orderOf_injective _ SemidirectProduct.inl_injective]; exact hn0ord)
  have hcommute'' : Commute (SemidirectProduct.inl n' :
      SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ'))
      (e (SemidirectProduct.inr k)) := by
    rw [← hx'eq]; exact hcommute'
  obtain ⟨-, hχ'k', hord⟩ :=
    order80_centralizer_elt_decomp hK hn'ord hd hcommute'' hyorder'
  exact h2 _ hχ'k' hord

/-- The centralizer (as a set) of an order-`5` element's `inl`-image bijects with `C₅ × ker χ`. -/
theorem order80_card_centralizer_eq {K : Type*} [Group K] [Finite K] {χ : K →* (ZMod 5)ˣ}
    {n0 : Multiplicative (ZMod 5)} (hn0 : orderOf n0 = 5) :
    Nat.card {x : SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ) //
        Commute (SemidirectProduct.inl n0) x} =
      5 * Nat.card {k : K // χ k = 1} := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hbij : Nat.card {x : SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ) //
        Commute (SemidirectProduct.inl n0) x} =
      Nat.card (Multiplicative (ZMod 5) × {k : K // χ k = 1}) := by
    apply Nat.card_congr
    refine
      { toFun := fun x => (x.1.left, ⟨x.1.right, ?_⟩)
        invFun := fun p => ⟨SemidirectProduct.inl p.1 * SemidirectProduct.inr p.2.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hmem := (order80_inl_gen_commute_iff hn0 x.1).mp x.2
      rwa [MonoidHom.comp_apply, ← MonoidHom.map_one unitAutHom,
        Function.Injective.eq_iff (unitAutHom_injective (p := 5))] at hmem
    · rw [order80_inl_gen_commute_iff hn0]
      simp [MonoidHom.comp_apply, p.2.2]
    · rintro ⟨x, hx⟩
      exact Subtype.ext (SemidirectProduct.inl_left_mul_inr_right x)
    · rintro ⟨a, k, hk⟩
      simp
  rw [hbij, Nat.card_prod]
  congr 1
  rw [Nat.card_eq_fintype_card]
  simp

/-- **Kernel-cardinality invariant for distinguishing semidirect products.** If `ker χ` and
`ker χ'` have different cardinalities, `C₅ ⋊[χ] K` and `C₅ ⋊[χ'] K` are not isomorphic. -/
theorem order80_ne_of_ker_card {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 5 (Fintype.card K)) {χ χ' : K →* (ZMod 5)ˣ}
    (hcard : Nat.card {k : K // χ k = 1} ≠ Nat.card {k : K // χ' k = 1}) :
    IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ) ≃*
      SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ')) := by
  constructor
  intro e
  apply hcard
  set n0 : Multiplicative (ZMod 5) := Multiplicative.ofAdd (1 : ZMod 5) with hn0
  have hn0ord : orderOf n0 = 5 := by
    rw [hn0, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hn0ord' : orderOf (e (SemidirectProduct.inl n0)) = 5 := by
    rw [MulEquiv.orderOf_eq, orderOf_injective _ SemidirectProduct.inl_injective]; exact hn0ord
  obtain ⟨n', hn'eq, hn'ord⟩ := order80_ord5_elt_eq_inl hK hn0ord'
  have hequiv : {x : SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ) //
        Commute (SemidirectProduct.inl n0) x} ≃
      {y : SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ') //
        Commute (SemidirectProduct.inl n') y} :=
    Equiv.subtypeEquiv e (fun x => by
      constructor
      · intro h; have := h.map e; rwa [hn'eq] at this
      · intro h; rw [← hn'eq] at h; have := h.map e.symm; simpa using this)
  have hcardeq := Nat.card_congr hequiv
  rw [order80_card_centralizer_eq hn0ord, order80_card_centralizer_eq hn'ord] at hcardeq
  omega

/-- Refinement of `order80_card_centralizer_eq` that additionally tracks the order `d` (not a
multiple of `5`) of the centralizing element. -/
theorem order80_card_centralizer_ord_eq {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 5 (Fintype.card K)) {χ : K →* (ZMod 5)ˣ}
    {n0 : Multiplicative (ZMod 5)} (hn0 : orderOf n0 = 5) {d : ℕ} (hd : ¬ (5 ∣ d)) :
    Nat.card {x : SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ) //
        Commute (SemidirectProduct.inl n0) x ∧ orderOf x = d} =
      Nat.card {k : K // χ k = 1 ∧ orderOf k = d} := by
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨SemidirectProduct.rightHom x.1,
        (order80_centralizer_elt_decomp hK hn0 hd x.2.1 x.2.2).2⟩
      invFun := fun p => ⟨SemidirectProduct.inr p.1, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [order80_inl_gen_commute_iff hn0]
    simp [MonoidHom.comp_apply, p.2.1]
  · rw [orderOf_injective _ SemidirectProduct.inr_injective]; exact p.2.2
  · rintro ⟨x, hx, hxord⟩
    obtain ⟨hxl, -, -⟩ := order80_centralizer_elt_decomp hK hn0 hd hx hxord
    apply Subtype.ext
    have hdecomp := SemidirectProduct.inl_left_mul_inr_right x
    rw [hxl, map_one, one_mul] at hdecomp
    exact hdecomp
  · rintro ⟨k, hk1, hkord⟩
    simp

/-- **Kernel-element-order-count invariant.** If `ker χ` and `ker χ'` have differing numbers of
elements of order `d` (not a multiple of `5`), then `C₅ ⋊[χ] K` and `C₅ ⋊[χ'] K` are not
isomorphic. -/
theorem order80_ne_of_ker_ord_count {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 5 (Fintype.card K)) {χ χ' : K →* (ZMod 5)ˣ} {d : ℕ} (hd : ¬ (5 ∣ d))
    (hcard : Nat.card {k : K // χ k = 1 ∧ orderOf k = d} ≠
      Nat.card {k : K // χ' k = 1 ∧ orderOf k = d}) :
    IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ) ≃*
      SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ')) := by
  constructor
  intro e
  apply hcard
  set n0 : Multiplicative (ZMod 5) := Multiplicative.ofAdd (1 : ZMod 5) with hn0
  have hn0ord : orderOf n0 = 5 := by
    rw [hn0, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hn0ord' : orderOf (e (SemidirectProduct.inl n0)) = 5 := by
    rw [MulEquiv.orderOf_eq, orderOf_injective _ SemidirectProduct.inl_injective]; exact hn0ord
  obtain ⟨n', hn'eq, hn'ord⟩ := order80_ord5_elt_eq_inl hK hn0ord'
  have hequiv : {x : SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ) //
        Commute (SemidirectProduct.inl n0) x ∧ orderOf x = d} ≃
      {y : SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ') //
        Commute (SemidirectProduct.inl n') y ∧ orderOf y = d} :=
    Equiv.subtypeEquiv e (fun x => by
      constructor
      · rintro ⟨h, hord⟩
        refine ⟨?_, ?_⟩
        · have := h.map e; rwa [hn'eq] at this
        · simp [hord]
      · rintro ⟨h, hord⟩
        refine ⟨?_, ?_⟩
        · rw [← hn'eq] at h; have := h.map e.symm; simpa using this
        · simpa using hord)
  have hcardeq := Nat.card_congr hequiv
  rw [order80_card_centralizer_ord_eq hK hn0ord hd,
    order80_card_centralizer_ord_eq hK hn'ord hd] at hcardeq
  omega

/-- An element has order exactly `2` iff it squares to `1` without being `1`. -/
theorem orderOf_eq_two_iff {G : Type*} [Group G] {k : G} : orderOf k = 2 ↔ k ^ 2 = 1 ∧ k ≠ 1 := by
  constructor
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one k, ?_⟩
    intro hk1
    rw [hk1, orderOf_one] at h
    norm_num at h
  · rintro ⟨hsq, hne⟩
    have hdvd : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h2

/-- **Kernel order-`2`-count invariant, phrased via `k² = 1 ∧ k ≠ 1` (decidable, unlike
`orderOf`).** If `ker χ` and `ker χ'` have differing numbers of order-`2` elements, the
semidirect products are not isomorphic. -/
theorem order80_ne_of_ker_sq_count {K : Type*} [Group K] [Fintype K]
    (hK : Nat.Coprime 5 (Fintype.card K)) {χ χ' : K →* (ZMod 5)ˣ}
    (hcard : Nat.card {k : K // χ k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} ≠
      Nat.card {k : K // χ' k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1}) :
    IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ) ≃*
      SemidirectProduct (Multiplicative (ZMod 5)) K (unitAutHom.comp χ')) := by
  apply order80_ne_of_ker_ord_count hK (d := 2) (by norm_num)
  have e1 : {k : K // χ k = 1 ∧ orderOf k = 2} ≃ {k : K // χ k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} :=
    Equiv.subtypeEquivRight (fun k => and_congr_right_iff.mpr fun _ => orderOf_eq_two_iff)
  have e2 : {k : K // χ' k = 1 ∧ orderOf k = 2} ≃ {k : K // χ' k = 1 ∧ k ^ 2 = 1 ∧ k ≠ 1} :=
    Equiv.subtypeEquivRight (fun k => and_congr_right_iff.mpr fun _ => orderOf_eq_two_iff)
  rw [Nat.card_congr e1, Nat.card_congr e2]
  exact hcard

/-! ## Element-order helpers, reused across `K₁`–`K₇` -/

/-- `IsEmpty` of a `MulEquiv` type is symmetric. -/
theorem isEmpty_mulEquiv_symm {A B : Type*} [Mul A] [Mul B] (h : IsEmpty (A ≃* B)) :
    IsEmpty (B ≃* A) :=
  ⟨fun e => h.false e.symm⟩

/-- If `x^(d/2) = 1` (with `d ≥ 2`), then `x` cannot have order exactly `d`. -/
theorem orderOf_ne_of_half_pow_eq_one {G : Type*} [Group G] {x : G} {d : ℕ} (hd2 : 2 ≤ d)
    (h : x ^ (d / 2) = 1) : orderOf x ≠ d := by
  intro heq
  have hdvd : orderOf x ∣ d / 2 := orderOf_dvd_of_pow_eq_one h
  rw [heq] at hdvd
  have hlt : d / 2 < d := Nat.div_lt_self (by omega) (by norm_num)
  have hpos : 0 < d / 2 := by omega
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

/-- If `x^d = 1` for `d = 2^e` (`e ≥ 1`) and `x^(d/2) ≠ 1`, then `x` has order exactly `d`. -/
theorem orderOf_eq_pow2_of {G : Type*} [Group G] {x : G} {d e : ℕ} (hd : d = 2 ^ e) (_he : 1 ≤ e)
    (h1 : x ^ d = 1) (h2 : x ^ (d / 2) ≠ 1) : orderOf x = d := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by rw [hd]; positivity) h1
  intro p hp hpd
  rw [hd] at hpd
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hpd
  have hpeq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp2
  rwa [hpeq]

/-- Powers of `order40_u4` (a chosen order-`4` unit) that equal `1` are exactly the multiples
of `4`. -/
theorem order40_u4_pow_eq_one_iff {n : ℕ} : order40_u4 ^ n = 1 ↔ 4 ∣ n := by
  constructor
  · intro h
    have hsplit : order40_u4 ^ n = order40_u4 ^ (n % 4) := by
      conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, order40_u4_pow_four, one_pow,
        one_mul]
    rw [hsplit] at h
    have hmod : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    set r := n % 4 with hr
    interval_cases r
    · exact Nat.dvd_of_mod_eq_zero hr.symm
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · rintro ⟨k, rfl⟩
    rw [pow_mul, order40_u4_pow_four, one_pow]

/-- Every element of `C₈` is a power of the additive generator. -/
theorem c8_elt_eq_gen_pow (x : C8g) :
    x = (Multiplicative.ofAdd (1 : ZMod 8)) ^ (Multiplicative.toAdd x).val := by
  rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from (ofAdd_toAdd _).symm]
  calc
    Multiplicative.ofAdd (Multiplicative.toAdd x) =
        Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ZMod 8)) := by
      rw [ZMod.natCast_zmod_val]
    _ = Multiplicative.ofAdd ((Multiplicative.toAdd x).val • (1 : ZMod 8)) := by simp
    _ = (Multiplicative.ofAdd (1 : ZMod 8)) ^ (Multiplicative.toAdd x).val := by rw [ofAdd_nsmul]

theorem c8_gen_pow_eight : (Multiplicative.ofAdd (1 : ZMod 8)) ^ 8 = 1 := by decide

/-- Any element of `C₈` with an even additive exponent has `x ^ 4 = 1`. -/
theorem c8_even_exp_pow4 {x : C8g} (h2 : 2 ∣ (Multiplicative.toAdd x).val) : x ^ 4 = 1 := by
  obtain ⟨m, hm⟩ := h2
  rw [c8_elt_eq_gen_pow x, hm, ← pow_mul, show 2 * m * 4 = 8 * m from by ring, pow_mul,
    c8_gen_pow_eight, one_pow]

/-- `ker (order40_chiC8_two)` consists exactly of the elements with `x ^ 4 = 1`. -/
theorem chiC8_two_ker_pow4 {x : C8g} (h : order40_chiC8_two x = 1) : x ^ 4 = 1 := by
  have hx := c8_elt_eq_gen_pow x
  rw [hx, map_pow, order40_chiC8_two_gen, ← pow_mul] at h
  have h4dvd : (4 : ℕ) ∣ 2 * (Multiplicative.toAdd x).val := order40_u4_pow_eq_one_iff.mp h
  have h2dvd : (2 : ℕ) ∣ (Multiplicative.toAdd x).val := by omega
  obtain ⟨m, hm⟩ := h2dvd
  rw [hx, hm, ← pow_mul, show 2 * m * 4 = 8 * m from by ring, pow_mul, c8_gen_pow_eight, one_pow]

/-- `ker (order40_chiC8_four)` consists exactly of the elements with `x ^ 2 = 1`. -/
theorem chiC8_four_ker_pow2 {x : C8g} (h : order40_chiC8_four x = 1) : x ^ 2 = 1 := by
  have hx := c8_elt_eq_gen_pow x
  rw [hx, map_pow, order40_chiC8_four_gen] at h
  obtain ⟨m, hm⟩ := order40_u4_pow_eq_one_iff.mp h
  rw [hx, hm, ← pow_mul, show 4 * m * 2 = 8 * m from by ring, pow_mul, c8_gen_pow_eight, one_pow]

/-- `ker (order40_chiC8_four_inv)` consists exactly of the elements with `x ^ 2 = 1`. -/
theorem chiC8_four_inv_ker_pow2 {x : C8g} (h : order40_chiC8_four_inv x = 1) : x ^ 2 = 1 := by
  have hx := c8_elt_eq_gen_pow x
  rw [hx, map_pow, order40_chiC8_four_inv_gen, ← pow_mul] at h
  have h4dvd : (4 : ℕ) ∣ 3 * (Multiplicative.toAdd x).val := order40_u4_pow_eq_one_iff.mp h
  have h4dvdn : (4 : ℕ) ∣ (Multiplicative.toAdd x).val := by omega
  obtain ⟨m, hm⟩ := h4dvdn
  rw [hx, hm, ← pow_mul, show 4 * m * 2 = 8 * m from by ring, pow_mul, c8_gen_pow_eight, one_pow]

/-- The kernel of `order40_c2UnitHom` is trivial. -/
theorem c2UnitHom_ker {y : Multiplicative (ZMod 2)} (h : order40_c2UnitHom y = 1) : y = 1 := by
  have hy : y = 1 ∨ y = Multiplicative.ofAdd (1 : ZMod 2) := by revert y; decide
  rcases hy with rfl | rfl
  · rfl
  · rw [order40_c2UnitHom_gen] at h; exact absurd h (by decide)

/-! ## `K₁ = C₈ × C₂` -/

/-! ### Two automorphisms of `K₁` generating the needed orbit moves

`K₁ = C₈ × C₂` with generators `g` (order `8`) and `h` (order `2`). We use:
* `K1_mulThree`: `(g, h) ↦ (g³, h)` — cubing on the `C₈` factor, identity on `C₂`.
* `K1_shear`: `(g, h) ↦ (g, g⁴h)` — shifts `h` by the order-`2` element `g⁴ ∈ ⟨g⟩`.
-/

/-- The automorphism of `K₁ = C₈ × C₂` cubing the `C₈`-generator and fixing the `C₂`-generator. -/
noncomputable def K1_mulThree : order16_wild_G1 ≃* order16_wild_G1 :=
  MulEquiv.prodCongr order40_C8_mulThree (MulEquiv.refl (Multiplicative (ZMod 2)))

theorem K1_mulThree_apply (x : C8g) (y : Multiplicative (ZMod 2)) :
    K1_mulThree (x, y) = (order40_C8_mulThree x, y) := rfl

/-- The automorphism of `K₁ = C₈ × C₂` sending `g ↦ gh`, `h ↦ h` — i.e. shears the `C₂`-part by
the image, mod `2`, of the `C₈`-exponent. Self-inverse since the shift term has order dividing
`2`. -/
noncomputable def K1_shear : order16_wild_G1 ≃* order16_wild_G1 where
  toFun p := (p.1, p.2 * Multiplicative.ofAdd
    ((ZMod.castHom (by norm_num : (2 : ℕ) ∣ 8) (ZMod 2)) (Multiplicative.toAdd p.1)))
  invFun p := (p.1, p.2 * Multiplicative.ofAdd
    ((ZMod.castHom (by norm_num : (2 : ℕ) ∣ 8) (ZMod 2)) (Multiplicative.toAdd p.1)))
  left_inv := by
    rintro ⟨x, y⟩
    ext <;> revert x y <;> decide
  right_inv := by
    rintro ⟨x, y⟩
    ext <;> revert x y <;> decide
  map_mul' := by
    rintro ⟨x1, y1⟩ ⟨x2, y2⟩
    ext <;> revert x1 y1 x2 y2 <;> decide

theorem K1_shear_apply (x : C8g) (y : Multiplicative (ZMod 2)) :
    K1_shear (x, y) = (x, y * Multiplicative.ofAdd
      ((ZMod.castHom (by norm_num : (2 : ℕ) ∣ 8) (ZMod 2)) (Multiplicative.toAdd x))) := rfl

/-! ### The `8` raw candidate characters, merged to `5` classes

`order80_classify_G1` narrows `χ` to `χ.comp inl ∈ {1, chiC8_four, chiC8_two, chiC8_four_inv}`
(`4` choices) and `χ.comp inr ∈ {1, c2UnitHom}` (`2` choices), giving `8` raw candidates
`χ_a_b := (a\text{-th }C_8\text{ character}).coprod (b\text{-th }C_2\text{ character})`. -/

noncomputable abbrev K1_chi_00 : order16_wild_G1 →* (ZMod 5)ˣ :=
  (1 : Multiplicative (ZMod 8) →* (ZMod 5)ˣ).coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)

noncomputable abbrev K1_chi_10 : order16_wild_G1 →* (ZMod 5)ˣ :=
  order40_chiC8_four.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)

noncomputable abbrev K1_chi_20 : order16_wild_G1 →* (ZMod 5)ˣ :=
  order40_chiC8_two.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)

noncomputable abbrev K1_chi_30 : order16_wild_G1 →* (ZMod 5)ˣ :=
  order40_chiC8_four_inv.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)

noncomputable abbrev K1_chi_02 : order16_wild_G1 →* (ZMod 5)ˣ :=
  (1 : Multiplicative (ZMod 8) →* (ZMod 5)ˣ).coprod order40_c2UnitHom

noncomputable abbrev K1_chi_12 : order16_wild_G1 →* (ZMod 5)ˣ :=
  order40_chiC8_four.coprod order40_c2UnitHom

noncomputable abbrev K1_chi_22 : order16_wild_G1 →* (ZMod 5)ˣ :=
  order40_chiC8_two.coprod order40_c2UnitHom

noncomputable abbrev K1_chi_32 : order16_wild_G1 →* (ZMod 5)ˣ :=
  order40_chiC8_four_inv.coprod order40_c2UnitHom

/-- `χ_{1,0}` and `χ_{3,0}` are in the same `Aut(K₁)`-orbit, via `K1_mulThree`. -/
theorem K1_chi_10_comp_mulThree : K1_chi_10.comp K1_mulThree.toMonoidHom = K1_chi_30 := by
  ext ⟨x, y⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, K1_mulThree_apply, MonoidHom.coprod_apply,
    MonoidHom.coprod_apply,
    show order40_chiC8_four (order40_C8_mulThree x) =
      (order40_chiC8_four.comp order40_C8_mulThree.toMonoidHom) x from rfl,
    order40_chiC8_four_comp_mulThree]

/-- `χ_{1,2}` and `χ_{3,2}` are in the same `Aut(K₁)`-orbit, via `K1_mulThree`. -/
theorem K1_chi_12_comp_mulThree : K1_chi_12.comp K1_mulThree.toMonoidHom = K1_chi_32 := by
  ext ⟨x, y⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, K1_mulThree_apply, MonoidHom.coprod_apply,
    MonoidHom.coprod_apply,
    show order40_chiC8_four (order40_C8_mulThree x) =
      (order40_chiC8_four.comp order40_C8_mulThree.toMonoidHom) x from rfl,
    order40_chiC8_four_comp_mulThree]

/-- The `C₂`-shift term used by `K1_shear`, composed with `order40_c2UnitHom`, agrees with
`order40_chiC8_two` on every element of `C₈` (both send `g^i ↦ u^{2(i \bmod 2)}`). -/
theorem K1_shift_eq_chiC8_two (x : Multiplicative (ZMod 8)) :
    order40_c2UnitHom (Multiplicative.ofAdd
      ((ZMod.castHom (by norm_num : (2 : ℕ) ∣ 8) (ZMod 2)) (Multiplicative.toAdd x))) =
      order40_chiC8_two x := by
  have hhom : order40_c2UnitHom.comp (MonoidHom.mk'
      (fun x : Multiplicative (ZMod 8) => Multiplicative.ofAdd
        ((ZMod.castHom (by norm_num : (2 : ℕ) ∣ 8) (ZMod 2)) (Multiplicative.toAdd x)))
      (fun a b => by simp [map_add, ofAdd_add])) = order40_chiC8_two := by
    apply order40_c8_unit_hom_ext
    rw [order40_chiC8_two_gen]
    change order40_c2UnitHom (Multiplicative.ofAdd
      ((ZMod.castHom (by norm_num : (2 : ℕ) ∣ 8) (ZMod 2))
        (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 8))))) = order40_u4 ^ 2
    rw [show (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 8) (ZMod 2))
      (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 8))) = (1 : ZMod 2) from by decide,
      order40_c2UnitHom_gen]
  exact DFunLike.congr_fun hhom x

/-- `χ_{0,2}` and `χ_{2,2}` are in the same `Aut(K₁)`-orbit, via `K1_shear`. -/
theorem K1_chi_02_comp_shear : K1_chi_02.comp K1_shear.toMonoidHom = K1_chi_22 := by
  ext ⟨x, y⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, K1_shear_apply, MonoidHom.coprod_apply,
    MonoidHom.coprod_apply, map_mul, K1_shift_eq_chiC8_two, MonoidHom.one_apply, one_mul, mul_comm]

/-! ### `K₁`'s isomorphism-class count: `5` -/

/-- **`K₁ = C₈ × C₂` contributes exactly `5` isomorphism classes** to the Sylow-`5`-unique
branch of the order-`80` classification: the `8` raw candidates from `order80_classify_G1`
collapse, via `K1_mulThree`/`K1_shear`, to the `5` representatives `K1_chi_00` (trivial action,
giving the abelian group `C₅ × K₁`), `K1_chi_20`, `K1_chi_10`, `K1_chi_02`, `K1_chi_12`. -/
theorem order80_classify_K1_reduced (φ' : order16_wild_G1 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_20)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_10)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_02)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
          (unitAutHom.comp K1_chi_12)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order80_classify_G1 φ'
  have hχ : χ = (χ.comp (MonoidHom.inl _ _)).coprod (χ.comp (MonoidHom.inr _ _)) :=
    (MonoidHom.coprod_unique χ).symm
  rcases hinl with h1 | h1 | h1 | h1 <;> rcases hinr with h2 | h2 <;>
    rw [h1, h2] at hχ <;> subst hχ
  · exact Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨e⟩
  · exact Or.inr <| Or.inl ⟨e⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨e.trans (semidirectProduct_of_comp_eq K1_shear K1_chi_02_comp_shear).some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨e.trans (semidirectProduct_of_comp_eq K1_mulThree K1_chi_10_comp_mulThree).some.symm⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨e.trans (semidirectProduct_of_comp_eq K1_mulThree K1_chi_12_comp_mulThree).some.symm⟩

/-! ### `K₁`'s `5` classes are pairwise distinct -/

theorem order16_wild_G1_coprime : Nat.Coprime 5 (Fintype.card order16_wild_G1) := by decide

/-- `1 : Multiplicative (ZMod 2)` squares to `1` (its order divides `2`). -/
theorem c2_sq_one (y : Multiplicative (ZMod 2)) : y ^ 2 = 1 := by revert y; decide

/-- `C₂` has exactly two elements. -/
theorem c2_elt_cases (y : Multiplicative (ZMod 2)) :
    y = 1 ∨ y = Multiplicative.ofAdd (1 : ZMod 2) := by revert y; decide

theorem c8_gen_orderOf : orderOf (Multiplicative.ofAdd (1 : ZMod 8)) = 8 :=
  orderOf_eq_pow2_of (e := 3) rfl (by norm_num) c8_gen_pow_eight (by decide)

theorem c8_gen_sq_orderOf : orderOf ((Multiplicative.ofAdd (1 : ZMod 8)) ^ 2) = 4 :=
  orderOf_eq_pow2_of (e := 2) rfl (by norm_num) (by rw [← pow_mul]; decide)
    (by rw [← pow_mul]; decide)

/-- `ker (K1_chi_20)` elements satisfy `k ^ 4 = 1`. -/
theorem K1_ker20_pow4 {x : C8g} {y : Multiplicative (ZMod 2)} (hk : K1_chi_20 (x, y) = 1) :
    (x, y) ^ 4 = 1 := by
  rw [show K1_chi_20 (x, y) = order40_chiC8_two x * (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ) y
      from MonoidHom.coprod_apply _ _ _, MonoidHom.one_apply, mul_one] at hk
  have hx4 := chiC8_two_ker_pow4 hk
  have hy4 : y ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, c2_sq_one]
  exact Prod.ext hx4 hy4

/-- `ker (K1_chi_10)` elements satisfy `k ^ 2 = 1`. -/
theorem K1_ker10_pow2 {x : C8g} {y : Multiplicative (ZMod 2)} (hk : K1_chi_10 (x, y) = 1) :
    (x, y) ^ 2 = 1 := by
  rw [show K1_chi_10 (x, y) = order40_chiC8_four x * (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ) y
      from MonoidHom.coprod_apply _ _ _, MonoidHom.one_apply, mul_one] at hk
  exact Prod.ext (chiC8_four_ker_pow2 hk) (c2_sq_one y)

/-- `ker (K1_chi_12)` elements satisfy `k ^ 4 = 1`. -/
theorem K1_ker12_pow4 {x : C8g} {y : Multiplicative (ZMod 2)} (hk : K1_chi_12 (x, y) = 1) :
    (x, y) ^ 4 = 1 := by
  rw [show K1_chi_12 (x, y) = order40_chiC8_four x * order40_c2UnitHom y from
    MonoidHom.coprod_apply _ _ _] at hk
  have hx := c8_elt_eq_gen_pow x
  rw [hx, map_pow, order40_chiC8_four_gen] at hk
  have h2n : (2 : ℕ) ∣ (Multiplicative.toAdd x).val := by
    rcases c2_elt_cases y with rfl | rfl
    · rw [map_one, mul_one] at hk
      have := order40_u4_pow_eq_one_iff.mp hk
      omega
    · rw [order40_c2UnitHom_gen, ← pow_add] at hk
      have h4dvd : (4 : ℕ) ∣ (Multiplicative.toAdd x).val + 2 := order40_u4_pow_eq_one_iff.mp hk
      omega
  have hx4 := c8_even_exp_pow4 h2n
  have hy4 : y ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, c2_sq_one]
  exact Prod.ext hx4 hy4

/-- `(g, 1)` (`g` the `C₈`-generator) lies in `ker (K1_chi_00)` and `ker (K1_chi_02)`, with
order `8`. -/
theorem K1_g1_ord8 : orderOf ((Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative (ZMod 2))) :
    order16_wild_G1) = 8 := by rw [Prod.orderOf_mk, c8_gen_orderOf, orderOf_one]; decide

theorem K1_g1_mem_ker02 : K1_chi_02 (Multiplicative.ofAdd (1 : ZMod 8), (1 : Multiplicative
    (ZMod 2))) = 1 := by
  rw [MonoidHom.coprod_apply]; simp

/-- `(g², 1)` lies in `ker (K1_chi_02)`, with order `4`. -/
theorem K1_g2_ord4 : orderOf (((Multiplicative.ofAdd (1 : ZMod 8)) ^ 2,
    (1 : Multiplicative (ZMod 2))) : order16_wild_G1) = 4 := by
  rw [Prod.orderOf_mk, c8_gen_sq_orderOf, orderOf_one]; decide

theorem K1_g2_mem_ker02 : K1_chi_02 (((Multiplicative.ofAdd (1 : ZMod 8)) ^ 2 : C8g),
    (1 : Multiplicative (ZMod 2))) = 1 := by
  rw [MonoidHom.coprod_apply]; simp

theorem K1_ne_00_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_20)) :=
  order80_ne_of_ker_order order16_wild_G1_coprime (d := 8) (by decide)
    ⟨_, rfl, K1_g1_ord8⟩
    (by
      rintro ⟨x, y⟩ hk
      exact orderOf_ne_of_half_pow_eq_one (by norm_num) (K1_ker20_pow4 hk))

theorem K1_ne_00_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_10)) :=
  order80_ne_of_ker_order order16_wild_G1_coprime (d := 8) (by decide)
    ⟨_, rfl, K1_g1_ord8⟩
    (by
      rintro ⟨x, y⟩ hk
      have h2 := K1_ker10_pow2 hk
      exact orderOf_ne_of_half_pow_eq_one (by norm_num) (show (x, y) ^ (8 / 2) = 1 by
        rw [show (8 / 2 : ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow]))

theorem K1_ne_00_12 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_12)) :=
  order80_ne_of_ker_order order16_wild_G1_coprime (d := 8) (by decide)
    ⟨_, rfl, K1_g1_ord8⟩
    (by
      rintro ⟨x, y⟩ hk
      exact orderOf_ne_of_half_pow_eq_one (by norm_num) (K1_ker12_pow4 hk))

theorem K1_ne_00_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_02)) :=
  order80_ne_of_ker_card order16_wild_G1_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide)

theorem K1_ne_20_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_10)) :=
  order80_ne_of_ker_order order16_wild_G1_coprime (d := 4) (by decide)
    ⟨_, by
      rw [MonoidHom.coprod_apply, map_pow, order40_chiC8_two_gen, MonoidHom.one_apply, mul_one,
        ← pow_mul, order40_u4_pow_four], K1_g2_ord4⟩
    (by
      rintro ⟨x, y⟩ hk
      exact orderOf_ne_of_half_pow_eq_one (by norm_num) (K1_ker10_pow2 hk))

/-- (Reversed via `isEmpty_mulEquiv_symm`.) -/
theorem K1_ne_02_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_20)) :=
  order80_ne_of_ker_order order16_wild_G1_coprime (d := 8) (by decide)
    ⟨_, K1_g1_mem_ker02, K1_g1_ord8⟩
    (by
      rintro ⟨x, y⟩ hk
      exact orderOf_ne_of_half_pow_eq_one (by norm_num) (K1_ker20_pow4 hk))

theorem K1_ne_20_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_02)) :=
  isEmpty_mulEquiv_symm K1_ne_02_20

theorem K1_ne_20_12 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_12)) :=
  order80_ne_of_ker_card order16_wild_G1_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide)

/-- (Reversed via `isEmpty_mulEquiv_symm`.) -/
theorem K1_ne_02_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_10)) :=
  order80_ne_of_ker_order order16_wild_G1_coprime (d := 4) (by decide)
    ⟨_, K1_g2_mem_ker02, K1_g2_ord4⟩
    (by
      rintro ⟨x, y⟩ hk
      exact orderOf_ne_of_half_pow_eq_one (by norm_num) (K1_ker10_pow2 hk))

theorem K1_ne_10_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_02)) :=
  isEmpty_mulEquiv_symm K1_ne_02_10

theorem c2_gen_orderOf : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 :=
  orderOf_eq_pow2_of (e := 1) rfl (by norm_num) (by decide) (by decide)

theorem K1_g2h_ord4 : orderOf (((Multiplicative.ofAdd (1 : ZMod 8)) ^ 2,
    Multiplicative.ofAdd (1 : ZMod 2)) : order16_wild_G1) = 4 := by
  rw [Prod.orderOf_mk, c8_gen_sq_orderOf, c2_gen_orderOf]; decide

theorem K1_g2h_mem_ker12 : K1_chi_12 (((Multiplicative.ofAdd (1 : ZMod 8)) ^ 2 : C8g),
    Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  rw [MonoidHom.coprod_apply, map_pow, order40_chiC8_four_gen, order40_c2UnitHom_gen,
    ← pow_add]
  decide

/-- (Reversed via `isEmpty_mulEquiv_symm`.) -/
theorem K1_ne_12_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_12) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_10)) :=
  order80_ne_of_ker_order order16_wild_G1_coprime (d := 4) (by decide)
    ⟨_, K1_g2h_mem_ker12, K1_g2h_ord4⟩
    (by
      rintro ⟨x, y⟩ hk
      exact orderOf_ne_of_half_pow_eq_one (by norm_num) (K1_ker10_pow2 hk))

theorem K1_ne_10_12 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_12)) :=
  isEmpty_mulEquiv_symm K1_ne_12_10

theorem K1_ne_02_12 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1
      (unitAutHom.comp K1_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G1 (unitAutHom.comp K1_chi_12)) :=
  order80_ne_of_ker_order order16_wild_G1_coprime (d := 8) (by decide)
    ⟨_, K1_g1_mem_ker02, K1_g1_ord8⟩
    (by
      rintro ⟨x, y⟩ hk
      exact orderOf_ne_of_half_pow_eq_one (by norm_num) (K1_ker12_pow4 hk))

/-! ## `K₂ = SD₁₆ = C₈ ⋊[φ₂] C₂`

Unlike `K₁`, `K₂` is non-abelian: `sgs⁻¹ = g³` for generators `g` (order `8`), `s` (order `2`).
The order-`8` elements of `K₂` are exactly `g, g³, g⁵, g⁷` (every outer element `sg^i` has order
`2` or `4`, by the semidihedral relation `(sg^i)² = g^{4i}`), so every automorphism sends
`g ↦ g^k` (`k` odd) and `s ↦ sg^{2m}`, and one computes directly that these act on a character
`χ = f₁.coprod f₂` (`f₁ = χ.comp inl`, `f₂ = χ.comp inr`) by `f₁ ↦ f₁^k`, `f₂ ↦ f₂ · f₁^{2m}`.
Since `f₁` is already forced to satisfy `f₁² = 1` (the invariance constraint from
`order80_classify_G2`), both `f₁^k = f₁` (`k` odd) and `f₁^{2m} = 1` — so **no automorphism of
`K₂` moves any of the `4` raw candidates**, and `K₂` contributes `4` distinct isomorphism
classes (no merging, unlike `K₁`). -/

/-- Conjugation by any element of an abelian group is trivial. -/
theorem mulAut_conj_of_comm {M : Type*} [CommGroup M] (m : M) : MulAut.conj m = 1 := by
  ext x
  simp [MulAut.conj_apply]

/-- For `B = C₂`, invariance of `f₁` under the generator's action extends to all of `B`. -/
theorem semidirectProduct_c2_compat {A M : Type*} [Group A] [CommGroup M]
    {φ : Multiplicative (ZMod 2) →* MulAut A} (f1 : A →* M)
    (hgen : f1.comp (φ (Multiplicative.ofAdd (1 : ZMod 2))).toMonoidHom = f1) :
    ∀ b : Multiplicative (ZMod 2), f1.comp (φ b).toMonoidHom = f1 := by
  intro b
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · ext a; simp
  · exact hgen

/-- `SemidirectProduct.lift`'s composite with `inl` recovers the first component. -/
theorem semidirectProduct_lift_comp_inl {A B M : Type*} [Group A] [Group B] [CommGroup M]
    {φ : B →* MulAut A} (f1 : A →* M) (f2 : B →* M)
    (h : ∀ b, f1.comp (φ b).toMonoidHom = (MulAut.conj (f2 b)).toMonoidHom.comp f1) :
    (SemidirectProduct.lift f1 f2 h).comp SemidirectProduct.inl = f1 := by
  ext n; exact SemidirectProduct.lift_inl f1 f2 h n

/-- `SemidirectProduct.lift`'s composite with `inr` recovers the second component. -/
theorem semidirectProduct_lift_comp_inr {A B M : Type*} [Group A] [Group B] [CommGroup M]
    {φ : B →* MulAut A} (f1 : A →* M) (f2 : B →* M)
    (h : ∀ b, f1.comp (φ b).toMonoidHom = (MulAut.conj (f2 b)).toMonoidHom.comp f1) :
    (SemidirectProduct.lift f1 f2 h).comp SemidirectProduct.inr = f2 := by
  ext n; exact SemidirectProduct.lift_inr f1 f2 h n

/-- The trivial character on `C₈` is (trivially) invariant under `c2Action_phi2`. -/
theorem K2_chiC8_one_invariant :
    ∀ b, (1 : Multiplicative (ZMod 8) →* (ZMod 5)ˣ).comp (c2Action_phi2 b).toMonoidHom = 1 :=
  fun _ => by ext; simp

/-- `order40_chiC8_two` is invariant under `c2Action_phi2`: this is exactly the constraint
established (as `hsq`) inside `order80_classify_G2`. -/
theorem K2_chiC8_two_invariant :
    ∀ b, order40_chiC8_two.comp (c2Action_phi2 b).toMonoidHom = order40_chiC8_two := by
  apply semidirectProduct_c2_compat
  apply order40_c8_unit_hom_ext
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    show c2Action_phi2 (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 8)) =
      phi2 (Multiplicative.ofAdd (1 : ZMod 8)) from by rw [c2Action_phi2_gen],
    phi2_gen, map_pow, order40_chiC8_two_gen]
  decide

/-- The `4` representative characters `K₂ → (ZMod 5)ˣ`, built via `SemidirectProduct.lift` from
the two invariant `C₈`-characters (`1`, `order40_chiC8_two`) and the two free `C₂`-characters
(`1`, `order40_c2UnitHom`). -/
noncomputable abbrev K2_chi_00 : order16_wild_G2 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 1
    (fun b => by rw [K2_chiC8_one_invariant, mulAut_conj_of_comm]; ext a; simp)

noncomputable abbrev K2_chi_02 : order16_wild_G2 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 order40_c2UnitHom
    (fun b => by rw [K2_chiC8_one_invariant, mulAut_conj_of_comm]; ext a; simp)

noncomputable abbrev K2_chi_20 : order16_wild_G2 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC8_two 1
    (fun b => by rw [K2_chiC8_two_invariant, mulAut_conj_of_comm]; ext a; simp)

noncomputable abbrev K2_chi_22 : order16_wild_G2 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC8_two order40_c2UnitHom
    (fun b => by rw [K2_chiC8_two_invariant, mulAut_conj_of_comm]; ext a; simp)

/-- **`K₂ = SD₁₆` contributes exactly `4` isomorphism classes**, with no merging needed: the `4`
raw candidates from `order80_classify_G2` are pairwise non-`Aut(K₂)`-equivalent. -/
theorem order80_classify_K2_reduced (φ' : order16_wild_G2 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 (unitAutHom.comp K2_chi_00)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 (unitAutHom.comp K2_chi_20)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2
          (unitAutHom.comp K2_chi_02)) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 φ' ≃*
        SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2
          (unitAutHom.comp K2_chi_22)) := by
  obtain ⟨χ, hinl, hinr, ⟨e⟩⟩ := order80_classify_G2 φ'
  rcases hinl with h1 | h1 <;> rcases hinr with h2 | h2
  · have hχ : χ = K2_chi_00 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inl ⟨e⟩
  · have hχ : χ = K2_chi_02 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K2_chi_20 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inl ⟨e⟩
  · have hχ : χ = K2_chi_22 := SemidirectProduct.hom_ext
      (h1.trans (semidirectProduct_lift_comp_inl _ _ _).symm)
      (h2.trans (semidirectProduct_lift_comp_inr _ _ _).symm)
    subst hχ; exact Or.inr <| Or.inr <| Or.inr ⟨e⟩

/-! ### `K₂`'s `4` classes are pairwise distinct -/

theorem order16_wild_G2_coprime : Nat.Coprime 5 (Fintype.card order16_wild_G2) := by decide

theorem K2_g_ord8 : orderOf (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8)) :
    order16_wild_G2) = 8 := by
  rw [orderOf_injective _ SemidirectProduct.inl_injective]; exact c8_gen_orderOf

theorem K2_ne_00_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2
      (unitAutHom.comp K2_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 (unitAutHom.comp K2_chi_20)) :=
  order80_ne_of_ker_order order16_wild_G2_coprime (d := 8) (by decide)
    ⟨_, rfl, K2_g_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K2_ne_00_22 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2
      (unitAutHom.comp K2_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 (unitAutHom.comp K2_chi_22)) :=
  order80_ne_of_ker_order order16_wild_G2_coprime (d := 8) (by decide)
    ⟨_, rfl, K2_g_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K2_ne_00_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2
      (unitAutHom.comp K2_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 (unitAutHom.comp K2_chi_02)) :=
  order80_ne_of_ker_card order16_wild_G2_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide)

/-- (Reversed via `isEmpty_mulEquiv_symm`.) -/
theorem K2_ne_02_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2
      (unitAutHom.comp K2_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 (unitAutHom.comp K2_chi_20)) :=
  order80_ne_of_ker_order order16_wild_G2_coprime (d := 8) (by decide)
    ⟨_, by decide, K2_g_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K2_ne_20_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2
      (unitAutHom.comp K2_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 (unitAutHom.comp K2_chi_02)) :=
  isEmpty_mulEquiv_symm K2_ne_02_20

theorem K2_ne_02_22 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2
      (unitAutHom.comp K2_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 (unitAutHom.comp K2_chi_22)) :=
  order80_ne_of_ker_order order16_wild_G2_coprime (d := 8) (by decide)
    ⟨_, by decide, K2_g_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

/-- The `(20, 22)` pair shares the same kernel cardinality (`8`) and order-spectrum (`{1,2,4}`),
so distinguishing them needs the finer order-`2`-count invariant. -/
theorem K2_ne_20_22 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2
      (unitAutHom.comp K2_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G2 (unitAutHom.comp K2_chi_22)) :=
  order80_ne_of_ker_sq_count order16_wild_G2_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide)

theorem zmod5_unit_pow_four (u : (ZMod 5)ˣ) : u ^ 4 = 1 := by revert u; decide

theorem phi3_eq_pow5 (a : C8g) : phi3 a = a ^ 5 := by
  rw [c8_elt_eq_gen_pow a, map_pow, phi3_gen, ← pow_mul, ← pow_mul, Nat.mul_comm]

theorem K3_lift_compat (f1 : C8g →* (ZMod 5)ˣ) (f2 : Multiplicative (ZMod 2) →*
    (ZMod 5)ˣ) : ∀ b, f1.comp (c2Action_phi3 b).toMonoidHom =
      (MulAut.conj (f2 b)).toMonoidHom.comp f1 := by
  intro b
  rw [mulAut_conj_of_comm]
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · rfl
  · apply order40_c8_unit_hom_ext
    change f1 (c2Action_phi3 (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd
      (1 : ZMod 8))) = f1 (Multiplicative.ofAdd (1 : ZMod 8))
    rw [show c2Action_phi3 (Multiplicative.ofAdd (1 : ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8)) = phi3 (Multiplicative.ofAdd (1 : ZMod 8)) from by
        rw [c2Action_phi3_gen],
      phi3_gen, map_pow, pow_succ, zmod5_unit_pow_four, one_mul]

/-! ### `K₃ = C₈ ⋊₅ C₂` (modular group `M₁₆`): the `8` raw candidates -/

noncomputable abbrev K3_chi_00 : order16_wild_G3 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 1 (K3_lift_compat 1 1)
noncomputable abbrev K3_chi_10 : order16_wild_G3 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC8_four 1 (K3_lift_compat _ _)
noncomputable abbrev K3_chi_20 : order16_wild_G3 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC8_two 1 (K3_lift_compat _ _)
noncomputable abbrev K3_chi_30 : order16_wild_G3 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC8_four_inv 1 (K3_lift_compat _ _)
noncomputable abbrev K3_chi_02 : order16_wild_G3 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 order40_c2UnitHom (K3_lift_compat _ _)
noncomputable abbrev K3_chi_12 : order16_wild_G3 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC8_four order40_c2UnitHom (K3_lift_compat _ _)
noncomputable abbrev K3_chi_22 : order16_wild_G3 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC8_two order40_c2UnitHom (K3_lift_compat _ _)
noncomputable abbrev K3_chi_32 : order16_wild_G3 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC8_four_inv order40_c2UnitHom (K3_lift_compat _ _)

theorem order16_wild_G3_coprime : Nat.Coprime 5 (Fintype.card order16_wild_G3) := by decide

/-- Kernel cardinalities of the `8` raw `K₃` candidates: `{00}=16`, `{20,02,22}=8` (a three-way
tie), `{10,30,12,32}=4` (a four-way tie).

Hand analysis of the order-`2`/`4`/`8` element counts within the cardinality-`8` tie (using
`(sg^i)² = g^{6i}` for `M₁₆`'s outer elements, unlike `SD₁₆`'s `g^{4i}`): `ker(20)` has counts
`(1,3,4,0)` for orders `(1,2,4,8)` — no order-`8` element, so `20` is distinguishable from `02`
and `22` via `order80_ne_of_ker_order` with `d = 8`. But `ker(02)` and `ker(22)` **both** have
counts `(1,1,2,4)` — identical order-spectra with multiplicity — so they are NOT distinguishable
by any order-existence or order-count invariant; either a finer invariant or (more likely) an
explicit `Aut(M₁₆)` automorphism merging `K3_chi_02` with `K3_chi_22` is needed. This mirrors the
`{10,30,12,32}` four-way tie, not yet analyzed. See `order80-k1-k2-classification.md` for the
general method to continue this. -/
theorem K3_chi_00_ker_card : Fintype.card {k : order16_wild_G3 // K3_chi_00 k = 1} = 16 := by
  decide
theorem K3_chi_10_ker_card : Fintype.card {k : order16_wild_G3 // K3_chi_10 k = 1} = 4 := by decide
theorem K3_chi_20_ker_card : Fintype.card {k : order16_wild_G3 // K3_chi_20 k = 1} = 8 := by decide
theorem K3_chi_30_ker_card : Fintype.card {k : order16_wild_G3 // K3_chi_30 k = 1} = 4 := by decide
theorem K3_chi_02_ker_card : Fintype.card {k : order16_wild_G3 // K3_chi_02 k = 1} = 8 := by decide
theorem K3_chi_12_ker_card : Fintype.card {k : order16_wild_G3 // K3_chi_12 k = 1} = 4 := by decide
theorem K3_chi_22_ker_card : Fintype.card {k : order16_wild_G3 // K3_chi_22 k = 1} = 8 := by decide
theorem K3_chi_32_ker_card : Fintype.card {k : order16_wild_G3 // K3_chi_32 k = 1} = 4 := by decide

/-! ### Resolving the `{02, 22}` tie: an explicit automorphism of `M₁₆` -/

/-- A hom out of `C₈` into any group, sending the generator to a chosen order-dividing-`8`
element. -/
noncomputable def C8_powHom {G : Type*} [Group G] (A : G) (hA : A ^ 8 = 1) :
    Multiplicative (ZMod 8) →* G :=
  MonoidHom.mk' (fun x => A ^ (Multiplicative.toAdd x).val) (by
    intro x y
    change A ^ (Multiplicative.toAdd (x * y)).val =
      A ^ (Multiplicative.toAdd x).val * A ^ (Multiplicative.toAdd y).val
    rw [← pow_add]
    have hval : (Multiplicative.toAdd (x * y)).val =
        ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) % 8 := by
      change (Multiplicative.toAdd x + Multiplicative.toAdd y).val = _
      rw [ZMod.val_add]
    rw [hval, ← Nat.div_add_mod ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) 8,
      pow_add, pow_mul, hA, one_pow, one_mul]
    congr 1
    omega)

/-- A hom out of `C₂` into any group, sending the generator to a chosen order-dividing-`2`
element. -/
noncomputable def C2_powHom {G : Type*} [Group G] (B : G) (hB : B ^ 2 = 1) :
    Multiplicative (ZMod 2) →* G :=
  MonoidHom.mk' (fun x => B ^ (Multiplicative.toAdd x).val) (by
    intro x y
    change B ^ (Multiplicative.toAdd (x * y)).val =
      B ^ (Multiplicative.toAdd x).val * B ^ (Multiplicative.toAdd y).val
    rw [← pow_add]
    have hval : (Multiplicative.toAdd (x * y)).val =
        ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) % 2 := by
      change (Multiplicative.toAdd x + Multiplicative.toAdd y).val = _
      rw [ZMod.val_add]
    rw [hval, ← Nat.div_add_mod ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val) 2,
      pow_add, pow_mul, hB, one_pow, one_mul]
    congr 1
    omega)

/-- Homomorphisms out of `C₈` into ANY monoid are determined by the generator (generic version
of `order40_c8_unit_hom_ext`, which is specific to `(ZMod 5)ˣ`). -/
theorem c8g_hom_ext {M : Type*} [Monoid M] {χ ψ : C8g →* M}
    (hgen : χ (Multiplicative.ofAdd (1 : ZMod 8)) = ψ (Multiplicative.ofAdd (1 : ZMod 8))) :
    χ = ψ := by
  apply MonoidHom.ext
  intro x
  rw [c8_elt_eq_gen_pow x, map_pow, map_pow, hgen]

/-- The element `A = (g, gen) ∈ M₁₆`: an order-`8` element in the "other" cyclic subgroup
`⟨A⟩ ≠ ⟨g⟩` (both index-`2` cyclic subgroups of `M₁₆`). -/
noncomputable def K3_A : order16_wild_G3 :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8)) *
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem K3_A_pow8 : K3_A ^ 8 = 1 := by decide

/-- `B = s`: the `C₂`-generator itself. -/
noncomputable def K3_B : order16_wild_G3 :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem K3_B_pow2 : K3_B ^ 2 = 1 := by decide

/-- The compatibility condition for `SemidirectProduct.lift (C8_powHom K3_A _) (C2_powHom K3_B _)`:
`B * A * B⁻¹ = A⁵` (i.e. `K3_B` conjugates `K3_A` exactly as `s` conjugates `g` in the original
presentation), verified by direct computation on the finite group. -/
theorem K3_tau_compat : ∀ b, (C8_powHom K3_A K3_A_pow8).comp (c2Action_phi3 b).toMonoidHom =
    (MulAut.conj ((C2_powHom K3_B K3_B_pow2) b)).toMonoidHom.comp (C8_powHom K3_A K3_A_pow8) := by
  intro b
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · apply c8g_hom_ext
    change (C8_powHom K3_A K3_A_pow8) (c2Action_phi3 (1 : Multiplicative (ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8))) =
      (MulAut.conj ((C2_powHom K3_B K3_B_pow2) (1 : Multiplicative (ZMod 2)))).toMonoidHom
        (C8_powHom K3_A K3_A_pow8 (Multiplicative.ofAdd (1 : ZMod 8)))
    decide
  · apply c8g_hom_ext
    change (C8_powHom K3_A K3_A_pow8) (c2Action_phi3 (Multiplicative.ofAdd (1 : ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8))) =
      (MulAut.conj ((C2_powHom K3_B K3_B_pow2) (Multiplicative.ofAdd (1 : ZMod 2)))).toMonoidHom
        (C8_powHom K3_A K3_A_pow8 (Multiplicative.ofAdd (1 : ZMod 8)))
    decide

/-- The candidate automorphism `τ : M₁₆ →* M₁₆` sending `g ↦ (g,gen)`, `s ↦ s`. -/
noncomputable def K3_tau : order16_wild_G3 →* order16_wild_G3 :=
  SemidirectProduct.lift (C8_powHom K3_A K3_A_pow8) (C2_powHom K3_B K3_B_pow2) K3_tau_compat

theorem K3_tau_bijective : Function.Bijective K3_tau := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def K3_tau_equiv : order16_wild_G3 ≃* order16_wild_G3 :=
  MulEquiv.ofBijective K3_tau K3_tau_bijective

/-- **`K3_chi_02` and `K3_chi_22` are `Aut(M₁₆)`-orbit-equivalent via `K3_tau_equiv`**,
confirming the merging predicted by their matching order-spectra: they give the SAME
isomorphism class, resolving the `{02,22}` half of the three-way `{20,02,22}` tie. -/
theorem K3_chi_02_comp_tau : K3_chi_02.comp K3_tau_equiv.toMonoidHom = K3_chi_22 := by
  apply MonoidHom.ext
  decide

/-- `K3` (`M₁₆`) contributes at most `3` isomorphism classes from `{00,20,02(=22),10,30,12,32}`
after the `02 = 22` merge — exact count of the remaining `{10,30,12,32}` four-way tie still
pending. -/
theorem K3_iso_02_22 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_22)) :=
  semidirectProduct_of_comp_eq K3_tau_equiv K3_chi_02_comp_tau

/-! ### Resolving the `{10, 30, 12, 32}` four-way tie -/

/-- `A₂ = g³ ∈ M₁₆` (a pure `C₈`-element, unlike `K3_A`). -/
noncomputable def K3_A2 : order16_wild_G3 :=
  SemidirectProduct.inl ((Multiplicative.ofAdd (1 : ZMod 8)) ^ 3)

theorem K3_A2_pow8 : K3_A2 ^ 8 = 1 := by decide

theorem K3_rho_compat : ∀ b, (C8_powHom K3_A2 K3_A2_pow8).comp (c2Action_phi3 b).toMonoidHom =
    (MulAut.conj ((C2_powHom K3_B K3_B_pow2) b)).toMonoidHom.comp (C8_powHom K3_A2 K3_A2_pow8) := by
  intro b
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · apply c8g_hom_ext
    change (C8_powHom K3_A2 K3_A2_pow8) (c2Action_phi3 (1 : Multiplicative (ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8))) =
      (MulAut.conj ((C2_powHom K3_B K3_B_pow2) (1 : Multiplicative (ZMod 2)))).toMonoidHom
        (C8_powHom K3_A2 K3_A2_pow8 (Multiplicative.ofAdd (1 : ZMod 8)))
    decide
  · apply c8g_hom_ext
    change (C8_powHom K3_A2 K3_A2_pow8) (c2Action_phi3 (Multiplicative.ofAdd (1 : ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8))) =
      (MulAut.conj ((C2_powHom K3_B K3_B_pow2) (Multiplicative.ofAdd (1 : ZMod 2)))).toMonoidHom
        (C8_powHom K3_A2 K3_A2_pow8 (Multiplicative.ofAdd (1 : ZMod 8)))
    decide

/-- The candidate automorphism `ρ : M₁₆ →* M₁₆` sending `g ↦ g³`, `s ↦ s` (cubing on the
`C₈`-part, analogous to `K1_mulThree`). -/
noncomputable def K3_rho : order16_wild_G3 →* order16_wild_G3 :=
  SemidirectProduct.lift (C8_powHom K3_A2 K3_A2_pow8) (C2_powHom K3_B K3_B_pow2) K3_rho_compat

theorem K3_rho_bijective : Function.Bijective K3_rho := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def K3_rho_equiv : order16_wild_G3 ≃* order16_wild_G3 :=
  MulEquiv.ofBijective K3_rho K3_rho_bijective

theorem K3_chi_10_comp_rho : K3_chi_10.comp K3_rho_equiv.toMonoidHom = K3_chi_30 := by
  apply MonoidHom.ext
  decide

theorem K3_chi_12_comp_rho : K3_chi_12.comp K3_rho_equiv.toMonoidHom = K3_chi_32 := by
  apply MonoidHom.ext
  decide

theorem K3_iso_10_30 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_30)) :=
  semidirectProduct_of_comp_eq K3_rho_equiv K3_chi_10_comp_rho

theorem K3_iso_12_32 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_12) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_32)) :=
  semidirectProduct_of_comp_eq K3_rho_equiv K3_chi_12_comp_rho

/-! ### `K₃`'s `5` surviving classes (`00, 20, 02(=22), 10(=30), 12(=32)`) are pairwise distinct -/

theorem K3_g_ord8 : orderOf (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8)) :
    order16_wild_G3) = 8 := by
  rw [orderOf_injective _ SemidirectProduct.inl_injective]; exact c8_gen_orderOf

theorem K3_g2_ord4 : orderOf (SemidirectProduct.inl ((Multiplicative.ofAdd (1 : ZMod 8)) ^ 2) :
    order16_wild_G3) = 4 := by
  rw [orderOf_injective _ SemidirectProduct.inl_injective]; exact c8_gen_sq_orderOf

theorem K3_g2gen_ord4 : orderOf ((SemidirectProduct.inl ((Multiplicative.ofAdd (1 : ZMod 8)) ^ 2) *
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) : order16_wild_G3) = 4 :=
  orderOf_eq_pow2_of (e := 2) rfl (by norm_num) (by decide) (by decide)

theorem K3_ne_00_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_20)) :=
  order80_ne_of_ker_order order16_wild_G3_coprime (d := 8) (by decide)
    ⟨_, rfl, K3_g_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K3_ne_00_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_10)) :=
  order80_ne_of_ker_order order16_wild_G3_coprime (d := 8) (by decide)
    ⟨_, rfl, K3_g_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K3_ne_00_12 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_12)) :=
  order80_ne_of_ker_order order16_wild_G3_coprime (d := 8) (by decide)
    ⟨_, rfl, K3_g_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K3_ne_00_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_02)) :=
  order80_ne_of_ker_card order16_wild_G3_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K3_chi_00_ker_card, K3_chi_02_ker_card]; decide)

/-- (Reversed via `isEmpty_mulEquiv_symm`.) -/
theorem K3_ne_02_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_20)) :=
  order80_ne_of_ker_order order16_wild_G3_coprime (d := 8) (by decide)
    ⟨_, by decide, K3_g_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K3_ne_20_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_02)) :=
  isEmpty_mulEquiv_symm K3_ne_02_20

theorem K3_ne_20_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_10)) :=
  order80_ne_of_ker_order order16_wild_G3_coprime (d := 4) (by decide)
    ⟨_, by decide, K3_g2_ord4⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (4 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K3_ne_20_12 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_12)) :=
  order80_ne_of_ker_card order16_wild_G3_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K3_chi_20_ker_card, K3_chi_12_ker_card]; decide)

/-- (Reversed via `isEmpty_mulEquiv_symm`.) -/
theorem K3_ne_02_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_10)) :=
  order80_ne_of_ker_order order16_wild_G3_coprime (d := 8) (by decide)
    ⟨_, by decide, K3_g_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K3_ne_10_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_02)) :=
  isEmpty_mulEquiv_symm K3_ne_02_10

theorem K3_ne_02_12 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_12)) :=
  order80_ne_of_ker_card order16_wild_G3_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K3_chi_02_ker_card, K3_chi_12_ker_card]; decide)

/-- (Reversed via `isEmpty_mulEquiv_symm`.) -/
theorem K3_ne_12_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_12) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_10)) :=
  order80_ne_of_ker_order order16_wild_G3_coprime (d := 4) (by decide)
    ⟨_, by decide, K3_g2gen_ord4⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (4 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K3_ne_10_12 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3
      (unitAutHom.comp K3_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G3 (unitAutHom.comp K3_chi_12)) :=
  isEmpty_mulEquiv_symm K3_ne_12_10

/-! ## `K₄ = D₁₆ = C₈ ⋊₇ C₂` (dihedral) -/

theorem K4_chiC8_one_invariant :
    ∀ b, (1 : Multiplicative (ZMod 8) →* (ZMod 5)ˣ).comp (c2Action_phi4 b).toMonoidHom = 1 :=
  fun _ => by ext; simp

theorem K4_chiC8_two_invariant :
    ∀ b, order40_chiC8_two.comp (c2Action_phi4 b).toMonoidHom = order40_chiC8_two := by
  apply semidirectProduct_c2_compat
  apply order40_c8_unit_hom_ext
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    show c2Action_phi4 (Multiplicative.ofAdd (1 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 8)) =
      phi4 (Multiplicative.ofAdd (1 : ZMod 8)) from by rw [c2Action_phi4_gen],
    phi4_gen, map_pow, order40_chiC8_two_gen]
  decide

noncomputable abbrev K4_chi_00 : order16_wild_G4 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 1
    (fun b => by rw [K4_chiC8_one_invariant, mulAut_conj_of_comm]; ext a; simp)

noncomputable abbrev K4_chi_02 : order16_wild_G4 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift 1 order40_c2UnitHom
    (fun b => by rw [K4_chiC8_one_invariant, mulAut_conj_of_comm]; ext a; simp)

noncomputable abbrev K4_chi_20 : order16_wild_G4 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC8_two 1
    (fun b => by rw [K4_chiC8_two_invariant, mulAut_conj_of_comm]; ext a; simp)

noncomputable abbrev K4_chi_22 : order16_wild_G4 →* (ZMod 5)ˣ :=
  SemidirectProduct.lift order40_chiC8_two order40_c2UnitHom
    (fun b => by rw [K4_chiC8_two_invariant, mulAut_conj_of_comm]; ext a; simp)

theorem order16_wild_G4_coprime : Nat.Coprime 5 (Fintype.card order16_wild_G4) := by decide

theorem K4_chi_00_ker_card : Fintype.card {k : order16_wild_G4 // K4_chi_00 k = 1} = 16 := by
  decide
theorem K4_chi_02_ker_card : Fintype.card {k : order16_wild_G4 // K4_chi_02 k = 1} = 8 := by decide
theorem K4_chi_20_ker_card : Fintype.card {k : order16_wild_G4 // K4_chi_20 k = 1} = 8 := by decide
theorem K4_chi_22_ker_card : Fintype.card {k : order16_wild_G4 // K4_chi_22 k = 1} = 8 := by decide

/-! ### Resolving the `{20, 22}` tie in `K₄ = D₁₆`

Both `ker(20)` and `ker(22)` have identical order-count profile `(1,5,2,0)` for orders
`(1,2,4,8)` (D₁₆'s outer/reflection elements are ALWAYS order `2`, unlike `M₁₆`'s), suggesting
they merge. The automorphism `σ : g ↦ g, s ↦ s·g` (verified: `σ(s)·g·σ(s)⁻¹ = g⁻¹`, matching the
defining relation) merges them. -/

noncomputable def K4_A : order16_wild_G4 :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))

theorem K4_A_pow8 : K4_A ^ 8 = 1 := by decide

noncomputable def K4_B : order16_wild_G4 :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8)) *
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

theorem K4_B_pow2 : K4_B ^ 2 = 1 := by decide

theorem K4_sigma_compat : ∀ b, (C8_powHom K4_A K4_A_pow8).comp (c2Action_phi4 b).toMonoidHom =
    (MulAut.conj ((C2_powHom K4_B K4_B_pow2) b)).toMonoidHom.comp (C8_powHom K4_A K4_A_pow8) := by
  intro b
  have hb : b = 1 ∨ b = Multiplicative.ofAdd (1 : ZMod 2) := by revert b; decide
  rcases hb with rfl | rfl
  · apply c8g_hom_ext
    change (C8_powHom K4_A K4_A_pow8) (c2Action_phi4 (1 : Multiplicative (ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8))) =
      (MulAut.conj ((C2_powHom K4_B K4_B_pow2) (1 : Multiplicative (ZMod 2)))).toMonoidHom
        (C8_powHom K4_A K4_A_pow8 (Multiplicative.ofAdd (1 : ZMod 8)))
    decide
  · apply c8g_hom_ext
    change (C8_powHom K4_A K4_A_pow8) (c2Action_phi4 (Multiplicative.ofAdd (1 : ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 8))) =
      (MulAut.conj ((C2_powHom K4_B K4_B_pow2) (Multiplicative.ofAdd (1 : ZMod 2)))).toMonoidHom
        (C8_powHom K4_A K4_A_pow8 (Multiplicative.ofAdd (1 : ZMod 8)))
    decide

noncomputable def K4_sigma : order16_wild_G4 →* order16_wild_G4 :=
  SemidirectProduct.lift (C8_powHom K4_A K4_A_pow8) (C2_powHom K4_B K4_B_pow2) K4_sigma_compat

theorem K4_sigma_bijective : Function.Bijective K4_sigma := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  rw [injective_iff_map_eq_one]
  decide

noncomputable def K4_sigma_equiv : order16_wild_G4 ≃* order16_wild_G4 :=
  MulEquiv.ofBijective K4_sigma K4_sigma_bijective

theorem K4_chi_20_comp_sigma : K4_chi_20.comp K4_sigma_equiv.toMonoidHom = K4_chi_22 := by
  apply MonoidHom.ext
  decide

theorem K4_iso_20_22 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4
      (unitAutHom.comp K4_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4 (unitAutHom.comp K4_chi_22)) :=
  semidirectProduct_of_comp_eq K4_sigma_equiv K4_chi_20_comp_sigma

/-! ### `K₄`'s `3` surviving classes (`00, 02, 20(=22)`) are pairwise distinct -/

theorem K4_g_ord8 : orderOf (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8)) :
    order16_wild_G4) = 8 := by
  rw [orderOf_injective _ SemidirectProduct.inl_injective]; exact c8_gen_orderOf

theorem K4_ne_00_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4
      (unitAutHom.comp K4_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4 (unitAutHom.comp K4_chi_02)) :=
  order80_ne_of_ker_card order16_wild_G4_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K4_chi_00_ker_card, K4_chi_02_ker_card]; decide)

theorem K4_ne_00_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4
      (unitAutHom.comp K4_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4 (unitAutHom.comp K4_chi_20)) :=
  order80_ne_of_ker_order order16_wild_G4_coprime (d := 8) (by decide)
    ⟨_, rfl, K4_g_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

/-- (Reversed via `isEmpty_mulEquiv_symm`.) -/
theorem K4_ne_02_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4
      (unitAutHom.comp K4_chi_02) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4 (unitAutHom.comp K4_chi_20)) :=
  order80_ne_of_ker_order order16_wild_G4_coprime (d := 8) (by decide)
    ⟨_, by decide, K4_g_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K4_ne_20_02 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4
      (unitAutHom.comp K4_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G4 (unitAutHom.comp K4_chi_02)) :=
  isEmpty_mulEquiv_symm K4_ne_02_20

/-! ## `K₆ = C₁₆` (cyclic) -/

noncomputable abbrev K6_chi_0 : Multiplicative (ZMod 16) →* (ZMod 5)ˣ := 1
noncomputable abbrev K6_chi_1 : Multiplicative (ZMod 16) →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 16) order40_u4 (by decide)
noncomputable abbrev K6_chi_2 : Multiplicative (ZMod 16) →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 16) (order40_u4 ^ 2) (by decide)
noncomputable abbrev K6_chi_3 : Multiplicative (ZMod 16) →* (ZMod 5)ˣ :=
  powHom (p := 5) (q := 16) (order40_u4 ^ 3) (by decide)

theorem order16_C16_coprime : Nat.Coprime 5 (Fintype.card (Multiplicative (ZMod 16))) := by decide

/-- The automorphism of `C₁₆` cubing the generator (unit `3` mod `16`). -/
noncomputable def K6_mulThree : Multiplicative (ZMod 16) ≃* Multiplicative (ZMod 16) :=
  unitAutHom (p := 16) (ZMod.unitOfCoprime 3 (by norm_num : Nat.Coprime 3 16))

theorem K6_chi_1_comp_mulThree : K6_chi_1.comp K6_mulThree.toMonoidHom = K6_chi_3 := by
  apply c16_hom_ext
  decide

theorem K6_ne_0_1 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5))
      (Multiplicative (ZMod 16)) (unitAutHom.comp K6_chi_0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16))
      (unitAutHom.comp K6_chi_1)) :=
  order80_ne_of_ker_card order16_C16_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide)

theorem K6_ne_0_2 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5))
      (Multiplicative (ZMod 16)) (unitAutHom.comp K6_chi_0) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16))
      (unitAutHom.comp K6_chi_2)) :=
  order80_ne_of_ker_card order16_C16_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide)

theorem K6_ne_1_2 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5))
      (Multiplicative (ZMod 16)) (unitAutHom.comp K6_chi_1) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16))
      (unitAutHom.comp K6_chi_2)) :=
  order80_ne_of_ker_card order16_C16_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide)

theorem K6_iso_1_3 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
      (Multiplicative (ZMod 16)) (unitAutHom.comp K6_chi_1) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 16))
      (unitAutHom.comp K6_chi_3)) :=
  semidirectProduct_of_comp_eq K6_mulThree K6_chi_1_comp_mulThree

/-! ## `K₇ = K₈ × C₂ = C₄ × C₂ × C₂` -/

noncomputable abbrev K7_chi_00 : order16_wild_G7 →* (ZMod 5)ˣ :=
  (1 : K8g →* (ZMod 5)ˣ).coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K7_chi_10 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_two.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K7_chi_20 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_snd_two.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K7_chi_30 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_prod_two.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K7_chi_40 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_four.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K7_chi_50 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_four_snd.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K7_chi_60 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_four_inv.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K7_chi_70 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_four_inv_snd.coprod (1 : Multiplicative (ZMod 2) →* (ZMod 5)ˣ)
noncomputable abbrev K7_chi_02 : order16_wild_G7 →* (ZMod 5)ˣ :=
  (1 : K8g →* (ZMod 5)ˣ).coprod order40_c2UnitHom
noncomputable abbrev K7_chi_12 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_two.coprod order40_c2UnitHom
noncomputable abbrev K7_chi_22 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_snd_two.coprod order40_c2UnitHom
noncomputable abbrev K7_chi_32 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_prod_two.coprod order40_c2UnitHom
noncomputable abbrev K7_chi_42 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_four.coprod order40_c2UnitHom
noncomputable abbrev K7_chi_52 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_four_snd.coprod order40_c2UnitHom
noncomputable abbrev K7_chi_62 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_four_inv.coprod order40_c2UnitHom
noncomputable abbrev K7_chi_72 : order16_wild_G7 →* (ZMod 5)ˣ :=
  order40_chiC4C2_fst_four_inv_snd.coprod order40_c2UnitHom

theorem order16_wild_G7_coprime : Nat.Coprime 5 (Fintype.card order16_wild_G7) := by decide

theorem K7_chi_00_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_00 k = 1} = 16 := by
  decide
theorem K7_chi_10_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_10 k = 1} = 8 := by decide
theorem K7_chi_20_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_20 k = 1} = 8 := by decide
theorem K7_chi_30_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_30 k = 1} = 8 := by decide
theorem K7_chi_40_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_40 k = 1} = 4 := by decide
theorem K7_chi_50_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_50 k = 1} = 4 := by decide
theorem K7_chi_60_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_60 k = 1} = 4 := by decide
theorem K7_chi_70_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_70 k = 1} = 4 := by decide
theorem K7_chi_02_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_02 k = 1} = 8 := by decide
theorem K7_chi_12_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_12 k = 1} = 8 := by decide
theorem K7_chi_22_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_22 k = 1} = 8 := by decide
theorem K7_chi_32_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_32 k = 1} = 8 := by decide
theorem K7_chi_42_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_42 k = 1} = 4 := by decide
theorem K7_chi_52_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_52 k = 1} = 4 := by decide
theorem K7_chi_62_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_62 k = 1} = 4 := by decide
theorem K7_chi_72_ker_card : Fintype.card {k : order16_wild_G7 // K7_chi_72 k = 1} = 4 := by decide

/-! ### `K₇`'s automorphisms: cubing `a`, and swapping `b`,`c` -/

/-- Inverting the `C₄`-part `a` (unit `3` mod `4`), fixing `b, c`. -/
noncomputable def K7_a_inv : Multiplicative (ZMod 4) ≃* Multiplicative (ZMod 4) :=
  unitAutHom (p := 4) (ZMod.unitOfCoprime 3 (by norm_num : Nat.Coprime 3 4))

noncomputable def K7_cube : order16_wild_G7 ≃* order16_wild_G7 :=
  MulEquiv.prodCongr (MulEquiv.prodCongr K7_a_inv (MulEquiv.refl _))
    (MulEquiv.refl (Multiplicative (ZMod 2)))

/-- Swapping the two `C₂`-factors `b` (inside `K₈g`) and `c` (the outer `C₂`). -/
noncomputable def K7_swapbc : order16_wild_G7 ≃* order16_wild_G7 where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv := by rintro ⟨⟨_, _⟩, _⟩; rfl
  right_inv := by rintro ⟨⟨_, _⟩, _⟩; rfl
  map_mul' := by rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩; rfl

theorem K7_chi_40_comp_cube : K7_chi_40.comp K7_cube.toMonoidHom = K7_chi_60 := by
  apply MonoidHom.ext; decide
theorem K7_chi_50_comp_cube : K7_chi_50.comp K7_cube.toMonoidHom = K7_chi_70 := by
  apply MonoidHom.ext; decide
theorem K7_chi_42_comp_cube : K7_chi_42.comp K7_cube.toMonoidHom = K7_chi_62 := by
  apply MonoidHom.ext; decide
theorem K7_chi_52_comp_cube : K7_chi_52.comp K7_cube.toMonoidHom = K7_chi_72 := by
  apply MonoidHom.ext; decide
theorem K7_chi_20_comp_swapbc : K7_chi_20.comp K7_swapbc.toMonoidHom = K7_chi_02 := by
  apply MonoidHom.ext; decide
theorem K7_chi_30_comp_swapbc : K7_chi_30.comp K7_swapbc.toMonoidHom = K7_chi_12 := by
  apply MonoidHom.ext; decide

/-- Shears the `C₄`-part `a` by the order-`2` element `2 ∈ ZMod 4` corresponding to `b`. -/
noncomputable def K7_shear_ab : order16_wild_G7 ≃* order16_wild_G7 where
  toFun p := ((p.1.1 * Multiplicative.ofAdd
      ((2 * (Multiplicative.toAdd p.1.2).val : ℕ) : ZMod 4), p.1.2), p.2)
  invFun p := ((p.1.1 * Multiplicative.ofAdd
      ((2 * (Multiplicative.toAdd p.1.2).val : ℕ) : ZMod 4), p.1.2), p.2)
  left_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  right_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  map_mul' := by
    rintro ⟨⟨x1, y1⟩, z1⟩ ⟨⟨x2, y2⟩, z2⟩
    ext <;> revert x1 y1 z1 x2 y2 z2 <;> decide

/-- `a`'s mod-`2` residue (used to build `K7_chi_10`, `_20`, ...) is preserved by `K7_shear_ab`:
this shear does NOT connect the `{20,02,22}`/`{30,12,32}` groups, confirming (together with
`K7_shear_ab` failing to relate `K7_chi_20`/`K7_chi_30`) that the `a mod 2` bit is a genuine
`Aut(K₇)`-invariant, distinguishing the two card-`8` classes. It DOES, however, connect the two
card-`4` classes, since `fst_four` (order-`4`, not just order-`2`) is not blind to this shift. -/
theorem K7_chi_40_comp_shear_ab : K7_chi_40.comp K7_shear_ab.toMonoidHom = K7_chi_50 := by
  apply MonoidHom.ext; decide

/-- Shears `b` by `c` (fixing `a, c`), mixing the `(b,c)`-plane. -/
noncomputable def K7_shear_bc : order16_wild_G7 ≃* order16_wild_G7 where
  toFun p := ((p.1.1, p.1.2 * p.2), p.2)
  invFun p := ((p.1.1, p.1.2 * p.2), p.2)
  left_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  right_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  map_mul' := by
    rintro ⟨⟨x1, y1⟩, z1⟩ ⟨⟨x2, y2⟩, z2⟩
    ext <;> revert x1 y1 z1 x2 y2 z2 <;> decide

theorem K7_chi_50_comp_swapbc : K7_chi_50.comp K7_swapbc.toMonoidHom = K7_chi_42 := by
  apply MonoidHom.ext; decide
theorem K7_chi_50_comp_shear_bc : K7_chi_50.comp K7_shear_bc.toMonoidHom = K7_chi_52 := by
  apply MonoidHom.ext; decide
theorem K7_chi_20_comp_shear_bc : K7_chi_20.comp K7_shear_bc.toMonoidHom = K7_chi_22 := by
  apply MonoidHom.ext; decide
theorem K7_chi_30_comp_shear_bc : K7_chi_30.comp K7_shear_bc.toMonoidHom = K7_chi_32 := by
  apply MonoidHom.ext; decide

/-! ### Merge theorems: `{20,02,22}`, `{30,12,32}`, and ALL of
`{40,50,60,70,42,52,62,72}` are single isomorphism classes -/

theorem K7_iso_20_02 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_02)) :=
  semidirectProduct_of_comp_eq K7_swapbc K7_chi_20_comp_swapbc

theorem K7_iso_20_22 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_22)) :=
  semidirectProduct_of_comp_eq K7_shear_bc K7_chi_20_comp_shear_bc

theorem K7_iso_30_12 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_30) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_12)) :=
  semidirectProduct_of_comp_eq K7_swapbc K7_chi_30_comp_swapbc

theorem K7_iso_30_32 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_30) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_32)) :=
  semidirectProduct_of_comp_eq K7_shear_bc K7_chi_30_comp_shear_bc

theorem K7_iso_40_50 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_40) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_50)) :=
  semidirectProduct_of_comp_eq K7_shear_ab K7_chi_40_comp_shear_ab

theorem K7_iso_40_60 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_40) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_60)) :=
  semidirectProduct_of_comp_eq K7_cube K7_chi_40_comp_cube

theorem K7_iso_50_70 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_50) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_70)) :=
  semidirectProduct_of_comp_eq K7_cube K7_chi_50_comp_cube

theorem K7_iso_50_42 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_50) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_42)) :=
  semidirectProduct_of_comp_eq K7_swapbc K7_chi_50_comp_swapbc

theorem K7_iso_50_52 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_50) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_52)) :=
  semidirectProduct_of_comp_eq K7_shear_bc K7_chi_50_comp_shear_bc

theorem K7_iso_42_62 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_42) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_62)) :=
  semidirectProduct_of_comp_eq K7_cube K7_chi_42_comp_cube

theorem K7_iso_52_72 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_52) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_72)) :=
  semidirectProduct_of_comp_eq K7_cube K7_chi_52_comp_cube

/-- **`K₇ = K₈ × C₂` contributes exactly `4` isomorphism classes**: `K7_chi_00` (trivial),
`K7_chi_10` (alone), `K7_chi_20` (representative for `{20,02,22,30,12,32}` — all `6` merge, see
`K7_iso_20_30` below and the `20/02/22`, `30/12/32` merges above), and `K7_chi_40`
(representative for all `8` of `{40,50,60,70,42,52,62,72}`). All `C(4,2)=6` pairs among these
representatives are proven distinct below. -/
theorem K7_a_ord4 : orderOf ((((Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 2))),
    (1 : Multiplicative (ZMod 2))) : order16_wild_G7)) = 4 :=
  orderOf_eq_pow2_of (e := 2) rfl (by norm_num) (by decide) (by decide)

/-- `(a, gen)` (with `gen` the `C₂`-generator inside `K₈g`), order `4`, lies in `ker(K7_chi_30)`. -/
theorem K7_ag_ord4 : orderOf ((((Multiplicative.ofAdd (1 : ZMod 4),
    Multiplicative.ofAdd (1 : ZMod 2)), (1 : Multiplicative (ZMod 2))) : order16_wild_G7)) = 4 :=
  orderOf_eq_pow2_of (e := 2) rfl (by norm_num) (by decide) (by decide)

theorem K7_ne_00_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_10)) :=
  order80_ne_of_ker_card order16_wild_G7_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K7_chi_00_ker_card, K7_chi_10_ker_card]; decide)

theorem K7_ne_00_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_20)) :=
  order80_ne_of_ker_card order16_wild_G7_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K7_chi_00_ker_card, K7_chi_20_ker_card]; decide)

theorem K7_ne_00_30 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_30)) :=
  order80_ne_of_ker_card order16_wild_G7_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K7_chi_00_ker_card, K7_chi_30_ker_card]; decide)

theorem K7_ne_00_40 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_00) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_40)) :=
  order80_ne_of_ker_card order16_wild_G7_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K7_chi_00_ker_card, K7_chi_40_ker_card]; decide)

theorem K7_ne_10_40 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_40)) :=
  order80_ne_of_ker_card order16_wild_G7_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K7_chi_10_ker_card, K7_chi_40_ker_card]; decide)

theorem K7_ne_20_40 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_40)) :=
  order80_ne_of_ker_card order16_wild_G7_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K7_chi_20_ker_card, K7_chi_40_ker_card]; decide)

theorem K7_ne_30_40 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_30) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_40)) :=
  order80_ne_of_ker_card order16_wild_G7_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K7_chi_30_ker_card, K7_chi_40_ker_card]; decide)

/-- (Reversed via `isEmpty_mulEquiv_symm`.) -/
theorem K7_ne_20_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_10)) :=
  order80_ne_of_ker_order order16_wild_G7_coprime (d := 4) (by decide)
    ⟨_, rfl, K7_a_ord4⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (4 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K7_ne_10_20 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_20)) :=
  isEmpty_mulEquiv_symm K7_ne_20_10

/-- (Reversed via `isEmpty_mulEquiv_symm`.) -/
theorem K7_ne_30_10 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_30) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_10)) :=
  order80_ne_of_ker_order order16_wild_G7_coprime (d := 4) (by decide)
    ⟨_, by decide, K7_ag_ord4⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (4 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K7_ne_10_30 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_10) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_30)) :=
  isEmpty_mulEquiv_symm K7_ne_30_10

/-! ### `K7_chi_20 ≅ K7_chi_30` after all: a `π`-shear resolves the last pair

`a²` being `Aut(K₇)`-fixed does NOT actually distinguish `20` from `30`: both `K7_chi_20 (a²)` and
`K7_chi_30 (a²)` are trivial (`snd_two`/`prod_two` both vanish at `a²`, since the `v2`-valued
combination squares to `1`). The real difference is in `χ(a)` itself (`20` vanishes there, `30`
doesn't) — but `a` itself is NOT `Aut(K₇)`-fixed (unlike `a²`), so this is not an obstruction.
Shearing `b` by `π(a)` (`π : C₄ → C₂` the mod-`2` projection, a ring/additive hom) merges them. -/

/-- The mod-`2` projection `C₄ → C₂`. -/
noncomputable def K7_pi : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (ZMod.castHom (by norm_num : (2:ℕ) ∣ 4) (ZMod 2)
    (Multiplicative.toAdd x))) (fun _ _ => by simp [ofAdd_add])

/-- Shears `b` by `π(a)` (fixing `a, c`): the automorphism merging `K7_chi_20` with
`K7_chi_30`. -/
noncomputable def K7_shear_piab : order16_wild_G7 ≃* order16_wild_G7 where
  toFun p := ((p.1.1, p.1.2 * K7_pi p.1.1), p.2)
  invFun p := ((p.1.1, p.1.2 * K7_pi p.1.1), p.2)
  left_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  right_inv := by rintro ⟨⟨x, y⟩, z⟩; ext <;> revert x y z <;> decide
  map_mul' := by
    rintro ⟨⟨x1, y1⟩, z1⟩ ⟨⟨x2, y2⟩, z2⟩
    ext <;> revert x1 y1 z1 x2 y2 z2 <;> decide

theorem K7_chi_20_comp_shear_piab : K7_chi_20.comp K7_shear_piab.toMonoidHom = K7_chi_30 := by
  apply MonoidHom.ext; decide

theorem K7_iso_20_30 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7
      (unitAutHom.comp K7_chi_20) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) order16_wild_G7 (unitAutHom.comp K7_chi_30)) :=
  semidirectProduct_of_comp_eq K7_shear_piab K7_chi_20_comp_shear_piab

/-! ## `K₅ = Q₁₆` (generalized quaternion) -/

theorem order16_Q16_coprime : Nat.Coprime 5 (Fintype.card (QuaternionGroup 4)) := by decide

theorem K5_chi_1_ker_card :
    Fintype.card {k : QuaternionGroup 4 // (1 : QuaternionGroup 4 →* (ZMod 5)ˣ) k = 1} = 16 := by
  decide
theorem K5_chi_c5_ker_card :
    Fintype.card {k : QuaternionGroup 4 // order80_chiQ16_c5 k = 1} = 8 := by decide
theorem K5_chi_xa_c5_ker_card :
    Fintype.card {k : QuaternionGroup 4 // order80_chiQ16_xa_c5 k = 1} = 8 := by decide
theorem K5_chi_prod_c5_ker_card :
    Fintype.card {k : QuaternionGroup 4 // order80_chiQ16_prod_c5 k = 1} = 8 := by decide

/-- Shifts the outer generator `x` by `a` (fixing `⟨a⟩` pointwise): candidate automorphism of
`Q₁₆` to test whether `order80_chiQ16_c5` and `order80_chiQ16_prod_c5` merge (both have kernel
cardinality `8` and order-count profile `(1,1,6,0)`). -/
noncomputable def K5_sigma : QuaternionGroup 4 ≃* QuaternionGroup 4 where
  toFun k := match k with
    | QuaternionGroup.a i => QuaternionGroup.a i
    | QuaternionGroup.xa i => QuaternionGroup.xa (i + 1)
  invFun k := match k with
    | QuaternionGroup.a i => QuaternionGroup.a i
    | QuaternionGroup.xa i => QuaternionGroup.xa (i - 1)
  left_inv := by rintro (i | i) <;> simp
  right_inv := by rintro (i | i) <;> simp
  map_mul' := by rintro (i | i) (j | j) <;> revert i j <;> decide

theorem K5_chi_c5_comp_sigma :
    order80_chiQ16_c5.comp K5_sigma.toMonoidHom = order80_chiQ16_prod_c5 := by
  apply MonoidHom.ext; decide

/-- **`K₅ = Q₁₆` contributes exactly `3` isomorphism classes**: `1` (trivial), `order80_chiQ16_c5`
(merged with `order80_chiQ16_prod_c5` via `K5_sigma`), and `order80_chiQ16_xa_c5`. -/
theorem K5_iso_c5_prod_c5 : Nonempty (SemidirectProduct (Multiplicative (ZMod 5))
      (QuaternionGroup 4) (unitAutHom.comp order80_chiQ16_c5) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
      (unitAutHom.comp order80_chiQ16_prod_c5)) :=
  semidirectProduct_of_comp_eq K5_sigma K5_chi_c5_comp_sigma

/-! ### `K₅`'s `3` classes are pairwise distinct -/

theorem K5_ne_1_c5 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
      (unitAutHom.comp (1 : QuaternionGroup 4 →* (ZMod 5)ˣ)) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
      (unitAutHom.comp order80_chiQ16_c5)) :=
  order80_ne_of_ker_card order16_Q16_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K5_chi_1_ker_card, K5_chi_c5_ker_card]; decide)

theorem K5_ne_1_xa_c5 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
      (unitAutHom.comp (1 : QuaternionGroup 4 →* (ZMod 5)ˣ)) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
      (unitAutHom.comp order80_chiQ16_xa_c5)) :=
  order80_ne_of_ker_card order16_Q16_coprime (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      K5_chi_1_ker_card, K5_chi_xa_c5_ker_card]; decide)

theorem K5_a1_ord8 : orderOf (QuaternionGroup.a (1 : ZMod (2 * 4)) : QuaternionGroup 4) = 8 :=
  orderOf_eq_pow2_of (e := 3) rfl (by norm_num) (by decide) (by decide)

/-- (Reversed via `isEmpty_mulEquiv_symm`.) -/
theorem K5_ne_xa_c5_c5 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
      (unitAutHom.comp order80_chiQ16_xa_c5) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
      (unitAutHom.comp order80_chiQ16_c5)) :=
  order80_ne_of_ker_order order16_Q16_coprime (d := 8) (by decide)
    ⟨_, by decide, K5_a1_ord8⟩
    (fun k hk => orderOf_ne_of_half_pow_eq_one (by norm_num)
      (show k ^ (8 / 2) = 1 by norm_num; revert hk; revert k; decide))

theorem K5_ne_c5_xa_c5 : IsEmpty (SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
      (unitAutHom.comp order80_chiQ16_c5) ≃*
    SemidirectProduct (Multiplicative (ZMod 5)) (QuaternionGroup 4)
      (unitAutHom.comp order80_chiQ16_xa_c5)) :=
  isEmpty_mulEquiv_symm K5_ne_xa_c5_c5

end Smallgroups.UsefulTheorems
