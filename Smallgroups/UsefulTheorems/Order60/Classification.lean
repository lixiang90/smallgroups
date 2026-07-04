/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order60.A5
import Smallgroups.UsefulTheorems.Order60.Semiproduct
import Smallgroups.UsefulTheorems.Counting

/-!
# Groups of order 60: complete classification

This file assembles `Order60.A5` (the `n₅ = 6` branch) and `Order60.Semiproduct` (the `n₅ = 1`
branch, `12` solvable representatives) into the **complete** classification of groups of order
`60`: there are exactly thirteen isomorphism classes (`sixty_isClassif`, `IsClassif 60 sixtyReps`).

## What is proved here

* **A reusable center-cardinality toolkit** for semidirect products `N ⋊[φ] K` with `N` abelian
  and every nontrivial automorphism in `range φ` fixed-point-free on `N` (true for
  `N = Multiplicative (ZMod p)`, any prime `p`): `mem_center_semidirectProduct_iff` /
  `card_center_semidirectProduct_of_fpf` show the center collapses to `{1} × (Z(K) ⊓ ker φ)`, and
  `card_ker_actionHom` / `card_center_cyclicNonabRep` turn this into an explicit `q / orderOf c`
  formula for the cyclic case `K = Multiplicative (ZMod q)`. Center cardinalities are computed
  for all twelve solvable representatives (`60, 60, 10, 10, 5, 6, 3, 6, 2, 1, 1, 2`), using
  explicit `Z(K) ⊓ ker φ` identification (`card_center_inf_ker_eq_one/two`) when `K` is
  non-abelian (`Dic₃` or `ℤ/2 × D₆`).
* **Full pairwise distinctness of all thirteen representatives** (`sixtyReps_pairwiseNonMulEquiv`):
  center cardinalities separate most pairs; the remaining ties are split by the existence of an
  order-`4` element (`sixtyRep_I` vs `II`, `III` vs `V`, `I_inv` vs `II_inv`, `III_inv` vs
  `V_sign`, `III_faithful` vs `V_inv`) or, against `A₅`, by simplicity versus a normal subgroup of
  order `5` (`III_faithful`, `V_inv` vs `A₅`).
* **Full exhaustiveness** (`sixty_classification`): every group of order `60` is isomorphic to one
  of the thirteen representatives. Built by transporting the structural decomposition
  `G ≅ N ⋊[φ] K` (`order60_structural_classification`) along abstract isomorphisms
  `N ≃* Multiplicative (ZMod 5)` (prime order) and `K ≃* fourP_X` (one of the five order-`12`
  types, `fourP_12_classification`), then pinning the transported action `φ` down to a named
  representative via the five `sixty_classify_fourP_*` theorems below — each classifies
  `Hom(K, Aut(ℤ/5))` up to the `Aut(K)`-orbit action, using explicit automorphisms of `K` built by
  hand for every case that needs one (inversion for `K = ℤ/12`/`Dic₃`; a shear/swap pair for
  `K = ℤ/2 × ℤ/6`; a shear for `K = ℤ/2 × D₆`; none for the cyclic-abelianization-coprime `K = A₄`).
* **`sixty_isClassif : IsClassif 60 sixtyReps`** bundles exhaustiveness and distinctness: there
  are exactly `13` isomorphism classes of groups of order `60`, matching the literature (`12`
  solvable classes plus the simple group `A₅`).
-/

namespace Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-! ### Coarse exhaustiveness -/

/-- **Structural exhaustiveness.** Every group of order `60` is either isomorphic to `A₅`, or
splits as a semidirect product `N ⋊[φ] K` with `N` (order `5`) normal and `K` order `12`. -/
theorem order60_structural_classification [Finite G] (hG : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) ∨
      ∃ (N K : Subgroup G) (φ : K →* MulAut N),
        N.Normal ∧ Nat.card N = 5 ∧ Nat.card K = 12 ∧
          Nonempty (G ≃* SemidirectProduct N K φ) := by
  rcases card_sylow_5_of_card_60 hG with h1 | h6
  · right; exact sixty_semidirectProduct hG h1
  · left; exact mulEquiv_alternatingGroup_of_card_60_of_card_sylow_5_eq_six hG h6

/-! ### A reusable center formula for semidirect products with a fixed-point-free action

If `N` is abelian and every nontrivial automorphism in the image of `φ : K →* MulAut N` has no
nontrivial fixed point (true for `N = ℤ/5`: every nontrivial element of `Aut(ℤ/5) ≅ (ZMod 5)ˣ`
acts freely on `ℤ/5 \ {1}`), the center of `N ⋊[φ] K` collapses to `{1} × (Z(K) ⊓ ker φ)`. This
single lemma computes the center of every non-trivial-action representative in
`Order60.Semiproduct` without a bespoke argument for each. -/

variable {N K : Type*} [CommGroup N] [Group K] {φ : K →* MulAut N}

theorem mem_center_semidirectProduct_iff
    (hfpf : ∀ k : K, φ k ≠ 1 → ∀ n : N, φ k n = n → n = 1)
    (hφne : ∃ k : K, φ k ≠ 1) (x : SemidirectProduct N K φ) :
    x ∈ Subgroup.center (SemidirectProduct N K φ) ↔
      x.left = 1 ∧ x.right ∈ Subgroup.center K ⊓ φ.ker := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hx
    have hker : φ x.right = 1 := by
      ext n
      have h := hx (⟨n, 1⟩ : SemidirectProduct N K φ)
      have hl := congrArg SemidirectProduct.left h
      simp only [SemidirectProduct.mul_left, map_one, MulAut.one_apply] at hl
      -- hl : n * x.left = x.left * (φ x.right) n
      have heq : x.left * n = x.left * (φ x.right) n := by rw [mul_comm x.left n]; exact hl
      exact (mul_left_cancel heq).symm
    have hzk : ∀ k : K, k * x.right = x.right * k := by
      intro k
      have h := hx (⟨1, k⟩ : SemidirectProduct N K φ)
      have hr := congrArg SemidirectProduct.right h
      simpa using hr
    have hleft1 : x.left = 1 := by
      obtain ⟨k, hk⟩ := hφne
      have h := hx (⟨1, k⟩ : SemidirectProduct N K φ)
      have hl := congrArg SemidirectProduct.left h
      simp only [SemidirectProduct.mul_left, one_mul, map_one, mul_one] at hl
      -- hl : (φ k) x.left = x.left
      exact hfpf k hk x.left hl
    exact ⟨hleft1, Subgroup.mem_center_iff.mpr hzk, MonoidHom.mem_ker.mpr hker⟩
  · rintro ⟨hleft1, hzk, hker⟩
    intro y
    apply SemidirectProduct.ext
    · change (y * x).left = (x * y).left
      simp [SemidirectProduct.mul_left, hleft1, MonoidHom.mem_ker.mp hker]
    · change (y * x).right = (x * y).right
      simp only [SemidirectProduct.mul_right]
      exact Subgroup.mem_center_iff.mp hzk y.right

/-- The cardinality form of `mem_center_semidirectProduct_iff`, ready to feed
`PairwiseNonMulEquiv.of_center_card`. -/
theorem card_center_semidirectProduct_of_fpf [Finite N] [Finite K]
    (hfpf : ∀ k : K, φ k ≠ 1 → ∀ n : N, φ k n = n → n = 1) (hφne : ∃ k : K, φ k ≠ 1) :
    Nat.card (Subgroup.center (SemidirectProduct N K φ)) =
      Nat.card (Subgroup.center K ⊓ φ.ker : Subgroup K) := by
  apply Nat.card_congr
  refine ⟨fun x => ⟨x.1.right, ((mem_center_semidirectProduct_iff hfpf hφne x.1).mp x.2).2⟩,
    fun z => ⟨⟨1, z.1⟩, (mem_center_semidirectProduct_iff hfpf hφne _).mpr ⟨rfl, z.2⟩⟩, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact (((mem_center_semidirectProduct_iff hfpf hφne x).mp hx).1).symm
    · rfl
  · rintro ⟨z, hz⟩
    rfl

/-- Every nontrivial automorphism of the multiplicative avatar of `ZMod p` (`p` prime,
equivalently of `ℤ/p`) is fixed-point-free: this is the key hypothesis feeding the center formula
above for every non-trivial-action representative in `Order60.Semiproduct` (`p = 5` for the
outer `ℤ/5` and `p = 3` for the `ℤ/3` inside `Dic₃ = ℤ/3 ⋊[-1] ℤ/4`). -/
theorem fpf_mulAut_multiplicative_zmod (p : ℕ) [Fact p.Prime]
    (σ : MulAut (Multiplicative (ZMod p))) (hσ : σ ≠ 1)
    (n : Multiplicative (ZMod p)) (hn : σ n = n) : n = 1 := by
  obtain ⟨u, rfl⟩ := exists_unitAutHom_eq σ
  have hnm : n = Multiplicative.ofAdd (Multiplicative.toAdd n) := (ofAdd_toAdd n).symm
  rw [hnm, unitAutHom_apply] at hn
  have hm : (u : ZMod p) * Multiplicative.toAdd n = Multiplicative.toAdd n := by
    simpa using congrArg Multiplicative.toAdd hn
  by_contra hne
  have hm0 : Multiplicative.toAdd n ≠ 0 := by
    intro h0
    apply hne
    rw [hnm, h0]
    rfl
  have hu1 : (u : ZMod p) = 1 := mul_right_cancel₀ hm0 (by rw [hm, one_mul])
  apply hσ
  have hueq : u = 1 := Units.ext hu1
  rw [hueq, map_one]

/-- **First isomorphism theorem, cardinality form.** `|ker φ| · |range φ| = |K|`. Used to compute
kernel sizes of the concrete actions in `Order60.Semiproduct` from the (easily computed) size of
their range. -/
theorem card_ker_mul_card_range {K T : Type*} [Group K] [Group T] [Finite K] (φ : K →* T) :
    Nat.card φ.ker * Nat.card φ.range = Nat.card K := by
  rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]

/-- Composing with an injective hom on the right does not change the size of the range: used to
strip off `unitAutHom` (injective, by `unitAutHom_injective`) when computing the size of the
range of `actionHom c hc = unitAutHom.comp (powHom c hc)`. -/
theorem card_range_comp_of_injective {K T T' : Type*} [Group K] [Group T] [Group T']
    (f : K →* T) {g : T →* T'} (hg : Function.Injective g) :
    Nat.card (g.comp f).range = Nat.card f.range := by
  rw [MonoidHom.range_comp, Subgroup.card_map_of_injective hg]

/-- The range of `powHom c hc : Multiplicative (ZMod q) →* (ZMod p)ˣ` is the cyclic subgroup
generated by `c`: `powHom c hc` sends the generator `Multiplicative.ofAdd 1` to `c` (up to the
degenerate case `q = 1`), and the range, being a subgroup containing `c`, must contain all of
`zpowers c`; conversely every value of `powHom c hc` is visibly a natural power of `c`. -/
theorem range_powHom_eq_zpowers {p q : ℕ} [NeZero q] (hq : 2 ≤ q) (c : (ZMod p)ˣ)
    (hc : c ^ q = 1) : (powHom c hc).range = Subgroup.zpowers c := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨((Multiplicative.toAdd x).val : ℤ), ?_⟩
    change c ^ ((Multiplicative.toAdd x).val : ℤ) = powHom c hc x
    rw [zpow_natCast]
    rfl
  · apply Subgroup.zpowers_le.mpr
    refine ⟨Multiplicative.ofAdd (1 : ZMod q), ?_⟩
    change c ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod q))).val = c
    rw [toAdd_ofAdd, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega), pow_one]

/-! ### Center cardinalities of the twelve solvable representatives

Combining the tools above: for a nontrivial action `φ : K →* MulAut (Multiplicative (ZMod p))`
with `K` cyclic (`Multiplicative (ZMod q)`), `Nat.card (center (SemidirectProduct _ K φ)) =
Nat.card K / orderOf c` where `c` is the unit realising `φ`. -/

private instance fact_prime_five' : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance fact_prime_three' : Fact (Nat.Prime 3) := ⟨by norm_num⟩

theorem orderOf_cInv : orderOf cInv = 2 := by
  have h2 : cInv ^ 2 = 1 := cInv_pow_two
  have hne : cInv ≠ 1 := cInv_ne_one
  have hdvd : orderOf cInv ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hne1 : orderOf cInv ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  have key : ∀ n ∈ Nat.divisors 2, n ≠ 1 → n = 2 := by decide
  exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hne1

theorem orderOf_cFaithful : orderOf cFaithful = 4 := by
  have h4 : cFaithful ^ 4 = 1 := cFaithful_pow_four
  have h2 : cFaithful ^ 2 ≠ 1 := cFaithful_pow_two_ne_one
  have hdvd : orderOf cFaithful ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hne2 : orderOf cFaithful ≠ 2 := fun h => h2 (h ▸ pow_orderOf_eq_one cFaithful)
  have hne1 : orderOf cFaithful ≠ 1 := by
    intro h
    apply h2
    rw [orderOf_eq_one_iff.mp h]
    exact one_pow 2
  have key : ∀ n ∈ Nat.divisors 4, n ≠ 1 → n ≠ 2 → n = 4 := by decide
  exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hne1 hne2

/-- Composing with a surjective hom on the right does not change the range. -/
theorem range_comp_of_surjective {K T T' : Type*} [Group K] [Group T] [Group T']
    (f : T →* T') {g : K →* T} (hg : Function.Surjective g) :
    (f.comp g).range = f.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective g hg]
  ext y
  simp [MonoidHom.mem_range]

/-- The kernel of a cyclic nontrivial action `actionHom c hc : Multiplicative (ZMod q) →*
MulAut (Multiplicative (ZMod p))` has size `q / orderOf c`. -/
theorem card_ker_actionHom {p q : ℕ} [NeZero q] [Fact p.Prime] (hq : 2 ≤ q) (c : (ZMod p)ˣ)
    (hc : c ^ q = 1) :
    Nat.card (actionHom c hc).ker * orderOf c = q := by
  have h1 := card_ker_mul_card_range (actionHom c hc)
  rw [actionHom, card_range_comp_of_injective (powHom c hc) unitAutHom_injective,
    range_powHom_eq_zpowers hq c hc, Nat.card_zpowers] at h1
  have hcardq : Nat.card (Multiplicative (ZMod q)) = q := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rwa [hcardq] at h1

/-- The center of `SemidirectProduct (Multiplicative (ZMod p)) (Multiplicative (ZMod q))
(actionHom c hc)`, for a nontrivial `c`, has size `q / orderOf c`. -/
theorem card_center_cyclicNonabRep {p q : ℕ} [NeZero q] [Fact p.Prime] (hq : 2 ≤ q) (c : (ZMod p)ˣ)
    (hc : c ^ q = 1) (hcne : c ≠ 1) :
    Nat.card (Subgroup.center (NonabRep c hc)) * orderOf c = q := by
  have hcenterK : Subgroup.center (Multiplicative (ZMod q)) = ⊤ := by
    ext x
    simp only [Subgroup.mem_center_iff, Subgroup.mem_top, iff_true]
    exact fun g => mul_comm g x
  have hpow : powHom c hc (Multiplicative.ofAdd (1 : ZMod q)) = c := by
    change c ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod q))).val = c
    rw [toAdd_ofAdd, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega), pow_one]
  have hφne : ∃ k : Multiplicative (ZMod q), actionHom c hc k ≠ 1 := by
    refine ⟨Multiplicative.ofAdd (1 : ZMod q), ?_⟩
    change unitAutHom (powHom c hc (Multiplicative.ofAdd (1 : ZMod q))) ≠ 1
    rw [hpow]
    intro hcontra
    exact hcne (unitAutHom_injective (by rw [hcontra, map_one]))
  have hker := card_ker_actionHom hq c hc
  have hzk : Subgroup.center (Multiplicative (ZMod q)) ⊓ (actionHom c hc).ker =
      (actionHom c hc).ker := by rw [hcenterK, top_inf_eq]
  change Nat.card (Subgroup.center (SemidirectProduct _ _ (actionHom c hc))) * orderOf c = q
  rw [card_center_semidirectProduct_of_fpf
    (fun k hk n hn => fpf_mulAut_multiplicative_zmod p (actionHom c hc k) hk n hn) hφne, hzk]
  exact hker

theorem card_center_sixtyRep_I_inv : Nat.card (Subgroup.center sixtyRep_I_inv) = 6 := by
  change Nat.card (Subgroup.center (NonabRep cInv cInv_pow_twelve)) = 6
  have h :=
  card_center_cyclicNonabRep (p := 5) (q := 12) (by norm_num) cInv cInv_pow_twelve cInv_ne_one
  rw [orderOf_cInv] at h
  omega

theorem card_center_sixtyRep_I_faithful : Nat.card (Subgroup.center sixtyRep_I_faithful) = 3 := by
  change Nat.card (Subgroup.center (NonabRep cFaithful cFaithful_pow_twelve)) = 3
  have h :=
  card_center_cyclicNonabRep (p := 5) (q := 12) (by norm_num) cFaithful cFaithful_pow_twelve
    (by decide)
  rw [orderOf_cFaithful] at h
  omega

theorem orderOf_neg_one_zmod_three : orderOf (-1 : (ZMod 3)ˣ) = 2 := by
  have h2 : (-1 : (ZMod 3)ˣ) ^ 2 = 1 := by decide
  have hne : (-1 : (ZMod 3)ˣ) ≠ 1 := by decide
  have hdvd : orderOf (-1 : (ZMod 3)ˣ) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hne1 : orderOf (-1 : (ZMod 3)ˣ) ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  have key : ∀ n ∈ Nat.divisors 2, n ≠ 1 → n = 2 := by decide
  exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hne1

theorem card_center_fourP_III_three : Nat.card (Subgroup.center (fourP_III 3)) = 2 := by
  change Nat.card (Subgroup.center (NonabRep (-1 : (ZMod 3)ˣ) (by decide : (-1:(ZMod 3)ˣ)^4=1))) = 2
  have h := card_center_cyclicNonabRep (p := 3) (q := 4) (by norm_num) (-1 : (ZMod 3)ˣ) (by decide)
    (by decide)
  rw [orderOf_neg_one_zmod_three] at h
  omega

/-! ### The five trivial-action (direct-product) representatives -/

private theorem card_mult_zmod_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

private theorem card_mult_zmod_five : Nat.card (Multiplicative (ZMod 5)) = 5 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem card_center_sixtyRep_I : Nat.card (Subgroup.center sixtyRep_I) = 60 := by
  change Nat.card (Subgroup.center (Multiplicative (ZMod 5) × fourP_I 3)) = 60
  rw [card_center_prod, card_center_eq_card_of_comm _ mul_comm,
    card_center_eq_card_of_comm _ mul_comm, card_mult_zmod_five, card_fourP_I]

theorem card_center_sixtyRep_II : Nat.card (Subgroup.center sixtyRep_II) = 60 := by
  change Nat.card (Subgroup.center (Multiplicative (ZMod 5) × fourP_II 3)) = 60
  rw [card_center_prod, card_center_eq_card_of_comm _ mul_comm,
    card_center_eq_card_of_comm _ mul_comm, card_mult_zmod_five, card_fourP_II]

theorem card_center_sixtyRep_III : Nat.card (Subgroup.center sixtyRep_III) = 10 := by
  change Nat.card (Subgroup.center (Multiplicative (ZMod 5) × fourP_III 3)) = 10
  rw [card_center_prod, card_center_eq_card_of_comm _ mul_comm,
    card_mult_zmod_five, card_center_fourP_III_three]

theorem card_center_sixtyRep_V : Nat.card (Subgroup.center sixtyRep_V) = 10 := by
  change Nat.card (Subgroup.center
    (Multiplicative (ZMod 5) × (Multiplicative (ZMod 2) × DihedralGroup 3))) = 10
  rw [card_center_prod, card_center_eq_card_of_comm _ mul_comm,
    card_center_prod, card_center_eq_card_of_comm _ mul_comm, card_mult_zmod_five,
    card_mult_zmod_two, DihedralGroup.center_eq_bot_of_odd_ne_one (by decide) (by norm_num),
    Subgroup.card_bot]

theorem card_center_sixtyRep_A4 : Nat.card (Subgroup.center sixtyRep_A4) = 5 := by
  change Nat.card (Subgroup.center (Multiplicative (ZMod 5) × alternatingGroup (Fin 4))) = 5
  rw [card_center_prod, card_center_eq_card_of_comm _ mul_comm, card_mult_zmod_five,
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]), Subgroup.card_bot]

/-! ### Splitting by the existence of an order-`4` element

Composing with the injective `inr` of a semidirect product (or the injective factor inclusion of
a direct product) transfers an order-`4` element of `K` to `G`; conversely (for our `K`s of order
`12`, coprime to `5`) the absence of an order-`4` element in `K` propagates to `G`, since
`Nat.card (Multiplicative (ZMod 5)) = 5` is odd and coprime to `4`. Concretely: `ℤ/12` and `Dic₃`
have an order-`4` element (`fourP_III_3_has_order4`), while `ℤ/2 × ℤ/6`, `ℤ/2 × D₆` and `A₄` do
not. -/

theorem fourP_V_three_no_order4 : ∀ g : fourP_V 3, orderOf g ≠ 4 := by
  rintro ⟨x, y⟩ h
  rw [Prod.orderOf_mk] at h
  have hx2 : orderOf x ∣ 2 := by
    have := orderOf_dvd_natCard x; rwa [card_mult_zmod_two] at this
  rcases y with i | i
  · have hy : orderOf (DihedralGroup.r i : DihedralGroup 3) ∣ 3 := by
      rw [DihedralGroup.orderOf_r]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left 3 i.val)
    have h3 : Nat.lcm (orderOf x) (orderOf (DihedralGroup.r i : DihedralGroup 3)) ∣ Nat.lcm 2 3 :=
      Nat.lcm_dvd (hx2.trans (Nat.dvd_lcm_left 2 3)) (hy.trans (Nat.dvd_lcm_right 2 3))
    rw [h] at h3
    norm_num at h3
  · rw [DihedralGroup.orderOf_sr] at h
    have h3 : Nat.lcm (orderOf x) 2 ∣ Nat.lcm 2 2 :=
      Nat.lcm_dvd (hx2.trans (Nat.dvd_lcm_left 2 2)) (Nat.dvd_lcm_right 2 2)
    rw [h] at h3
    norm_num at h3

theorem sixtyRep_I_has_order4 : ∃ g : sixtyRep_I, orderOf g = 4 := by
  have hg12 : orderOf (Multiplicative.ofAdd (1 : ZMod 12)) = 12 := by
    rw [orderOf_ofAdd_eq_addOrderOf]; exact ZMod.addOrderOf_one 12
  refine ⟨(1, (Multiplicative.ofAdd (1 : ZMod 12)) ^ 3), ?_⟩
  change orderOf ((1 : Multiplicative (ZMod 5)), (Multiplicative.ofAdd (1 : ZMod 12)) ^ 3) = 4
  rw [Prod.orderOf_mk, orderOf_one, orderOf_pow, hg12]
  norm_num

theorem sixtyRep_II_no_order4 : ∀ g : sixtyRep_II, orderOf g ≠ 4 := by
  rintro ⟨a, b, c⟩ h
  rw [Prod.orderOf_mk, Prod.orderOf_mk] at h
  have ha : orderOf a ∣ 5 := by
    have := orderOf_dvd_natCard a; rwa [card_mult_zmod_five] at this
  have hb : orderOf b ∣ 2 := by
    have := orderOf_dvd_natCard b; rwa [card_mult_zmod_two] at this
  have hc : orderOf c ∣ 6 := by
    have hcard6 : Nat.card (Multiplicative (ZMod 6)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have := orderOf_dvd_natCard c; rwa [hcard6] at this
  have hbnd : Nat.lcm (orderOf a) (Nat.lcm (orderOf b) (orderOf c)) ∣ Nat.lcm 5 (Nat.lcm 2 6) :=
    Nat.lcm_dvd (ha.trans (Nat.dvd_lcm_left 5 (Nat.lcm 2 6)))
      (Nat.lcm_dvd (hb.trans ((Nat.dvd_lcm_left 2 6).trans (Nat.dvd_lcm_right 5 (Nat.lcm 2 6))))
        (hc.trans ((Nat.dvd_lcm_right 2 6).trans (Nat.dvd_lcm_right 5 (Nat.lcm 2 6)))))
  rw [h] at hbnd
  norm_num at hbnd

/-! ### Distinctness of the seven fully-computed representatives

Combining the center cardinalities above (`60, 60, 10, 10, 5, 6, 3`) with the order-`4`-element
split (`sixtyRep_I` has one, `sixtyRep_II` does not — resolving the one center tie) shows these
seven representatives are pairwise non-isomorphic. The remaining five (`II_inv`, `III_inv`,
`III_faithful`, `V_inv`, `V_sign`) are not yet distinguished — see the module docstring. -/

private theorem sixtyRep_distinct_of_center_and_order4
    {A B : Type} [Group A] [Group B] {ca cb : ℕ}
    (hca : Nat.card (Subgroup.center A) = ca) (hcb : Nat.card (Subgroup.center B) = cb)
    (hne : ca ≠ cb) : ¬ Nonempty (A ≃* B) :=
  not_nonempty_mulEquiv_of_card_center_ne (by rw [hca, hcb]; exact hne)

theorem sixtyRep_I_ne_II : ¬ Nonempty (sixtyRep_I ≃* sixtyRep_II) := by
  rintro ⟨e⟩
  obtain ⟨g, hg⟩ := sixtyRep_I_has_order4
  exact sixtyRep_II_no_order4 (e g) (by rw [MulEquiv.orderOf_eq e g, hg])

theorem sixtyRep_I_ne_III : ¬ Nonempty (sixtyRep_I ≃* sixtyRep_III) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_I card_center_sixtyRep_III
    (by norm_num)

theorem sixtyRep_I_ne_V : ¬ Nonempty (sixtyRep_I ≃* sixtyRep_V) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_I card_center_sixtyRep_V
    (by norm_num)

theorem sixtyRep_I_ne_A4 : ¬ Nonempty (sixtyRep_I ≃* sixtyRep_A4) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_I card_center_sixtyRep_A4
    (by norm_num)

theorem sixtyRep_I_ne_I_inv : ¬ Nonempty (sixtyRep_I ≃* sixtyRep_I_inv) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_I card_center_sixtyRep_I_inv
    (by norm_num)

theorem sixtyRep_I_ne_I_faithful : ¬ Nonempty (sixtyRep_I ≃* sixtyRep_I_faithful) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_I card_center_sixtyRep_I_faithful
    (by norm_num)

theorem sixtyRep_II_ne_III : ¬ Nonempty (sixtyRep_II ≃* sixtyRep_III) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_II card_center_sixtyRep_III
    (by norm_num)

theorem sixtyRep_II_ne_V : ¬ Nonempty (sixtyRep_II ≃* sixtyRep_V) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_II card_center_sixtyRep_V
    (by norm_num)

theorem sixtyRep_II_ne_A4 : ¬ Nonempty (sixtyRep_II ≃* sixtyRep_A4) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_II card_center_sixtyRep_A4
    (by norm_num)

theorem sixtyRep_II_ne_I_inv : ¬ Nonempty (sixtyRep_II ≃* sixtyRep_I_inv) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_II card_center_sixtyRep_I_inv
    (by norm_num)

theorem sixtyRep_II_ne_I_faithful : ¬ Nonempty (sixtyRep_II ≃* sixtyRep_I_faithful) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_II card_center_sixtyRep_I_faithful
    (by norm_num)

theorem sixtyRep_III_has_order4 : ∃ g : sixtyRep_III, orderOf g = 4 := by
  obtain ⟨g, hg⟩ := fourP_III_3_has_order4
  refine ⟨((1 : Multiplicative (ZMod 5)), g), ?_⟩
  change orderOf ((1 : Multiplicative (ZMod 5)), g) = 4
  rw [Prod.orderOf_mk, orderOf_one, hg]
  norm_num

/-- `sixtyRep_III` and `sixtyRep_V` share center size `10` (both split off `ℤ/5`), but only
`Dic₃` has an order-`4` element, not `ℤ/2 × D₆`. -/
theorem sixtyRep_III_ne_V : ¬ Nonempty (sixtyRep_III ≃* sixtyRep_V) := by
  rintro ⟨e⟩
  obtain ⟨g, hg⟩ := sixtyRep_III_has_order4
  set h := e g with hh
  have hprod : orderOf h = Nat.lcm (orderOf h.1) (orderOf h.2) := by
    rw [hh]; conv_lhs => rw [← Prod.mk.eta (p := e g)]
    exact Prod.orderOf_mk
  have heq4 : orderOf h = 4 := by rw [hh, MulEquiv.orderOf_eq e g, hg]
  have h1 : orderOf h.1 ∣ 5 := by
    have := orderOf_dvd_natCard h.1; rwa [card_mult_zmod_five] at this
  have h1' : orderOf h.1 = 1 ∨ orderOf h.1 = 5 := (Nat.dvd_prime (by norm_num)).mp h1
  have horder2 : orderOf h.2 = 4 := by
    rcases h1' with h1a | h1a
    · rw [heq4, h1a, Nat.lcm_one_left] at hprod
      omega
    · exfalso
      rw [heq4, h1a] at hprod
      have hdvd5 : (5 : ℕ) ∣ 4 := hprod ▸ Nat.dvd_lcm_left 5 (orderOf h.2)
      omega
  exact fourP_V_three_no_order4 h.2 horder2

theorem sixtyRep_III_ne_A4 : ¬ Nonempty (sixtyRep_III ≃* sixtyRep_A4) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_III card_center_sixtyRep_A4
    (by norm_num)

theorem sixtyRep_III_ne_I_inv : ¬ Nonempty (sixtyRep_III ≃* sixtyRep_I_inv) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_III card_center_sixtyRep_I_inv
    (by norm_num)

theorem sixtyRep_III_ne_I_faithful : ¬ Nonempty (sixtyRep_III ≃* sixtyRep_I_faithful) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_III card_center_sixtyRep_I_faithful
    (by norm_num)

theorem sixtyRep_V_ne_A4 : ¬ Nonempty (sixtyRep_V ≃* sixtyRep_A4) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_V card_center_sixtyRep_A4
    (by norm_num)

theorem sixtyRep_V_ne_I_inv : ¬ Nonempty (sixtyRep_V ≃* sixtyRep_I_inv) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_V card_center_sixtyRep_I_inv
    (by norm_num)

theorem sixtyRep_V_ne_I_faithful : ¬ Nonempty (sixtyRep_V ≃* sixtyRep_I_faithful) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_V card_center_sixtyRep_I_faithful
    (by norm_num)

theorem sixtyRep_A4_ne_I_inv : ¬ Nonempty (sixtyRep_A4 ≃* sixtyRep_I_inv) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_A4 card_center_sixtyRep_I_inv
    (by norm_num)

theorem sixtyRep_A4_ne_I_faithful : ¬ Nonempty (sixtyRep_A4 ≃* sixtyRep_I_faithful) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_A4 card_center_sixtyRep_I_faithful
    (by norm_num)

theorem sixtyRep_I_inv_ne_I_faithful : ¬ Nonempty (sixtyRep_I_inv ≃* sixtyRep_I_faithful) :=
  sixtyRep_distinct_of_center_and_order4 card_center_sixtyRep_I_inv card_center_sixtyRep_I_faithful
    (by norm_num)

/-! ### Centers of the five remaining representatives

The five representatives with a nontrivial action on a complement `K` that is non-abelian
(`Dic₃`, `ℤ/2 × D₆`) or whose kernel is a proper subgroup of an abelian `K` (`ℤ/2 × ℤ/6`) need
`Z(K) ⊓ ker φ` itself, not just cardinality arithmetic. Since `|Z(K)| = 2` in the non-abelian
cases, with an explicit central generator `z`, the intersection is all of `Z(K)` or trivial
according to whether `φ z = 1`. -/

private instance finiteSemidirectProduct {N K : Type*} [Group N] [Group K] [Finite N] [Finite K]
    {φ : K →* MulAut N} : Finite (SemidirectProduct N K φ) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

private theorem unitAutHom_ne_one {p : ℕ} [Fact p.Prime] {u : (ZMod p)ˣ} (hu : u ≠ 1) :
    unitAutHom u ≠ 1 :=
  fun h => hu (unitAutHom_injective (by rw [h, map_one]))

/-- If `Z(K)` has order `2` with central witness `z ≠ 1` and `ψ z = 1`, then
`Z(K) ⊓ ker ψ = Z(K)` has order `2`. -/
theorem card_center_inf_ker_eq_two {K T : Type*} [Group K] [Group T] [Finite K]
    (hZ : Nat.card (Subgroup.center K) = 2) {z : K} (hz : z ∈ Subgroup.center K) (hzne : z ≠ 1)
    {ψ : K →* T} (h1 : ψ z = 1) :
    Nat.card (Subgroup.center K ⊓ ψ.ker : Subgroup K) = 2 := by
  have hordvd : orderOf z ∣ 2 := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hz)
    rwa [Nat.card_zpowers, hZ] at h
  have hord : orderOf z = 2 := by
    have hne1 : orderOf z ≠ 1 := fun h => hzne (orderOf_eq_one_iff.mp h)
    have key : ∀ n ∈ Nat.divisors 2, n ≠ 1 → n = 2 := by decide
    exact key _ (Nat.mem_divisors.mpr ⟨hordvd, by norm_num⟩) hne1
  have hle : Subgroup.zpowers z ≤ Subgroup.center K ⊓ ψ.ker :=
    le_inf (Subgroup.zpowers_le.mpr hz) (Subgroup.zpowers_le.mpr (MonoidHom.mem_ker.mpr h1))
  have hdvd1 : 2 ∣ Nat.card (Subgroup.center K ⊓ ψ.ker : Subgroup K) := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hord] at h
  have hdvd2 : Nat.card (Subgroup.center K ⊓ ψ.ker : Subgroup K) ∣ 2 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left (a := Subgroup.center K) (b := ψ.ker))
    rwa [hZ] at h
  exact Nat.dvd_antisymm hdvd2 hdvd1

/-- If `Z(K)` has order `2` with central witness `z` and `ψ z ≠ 1`, then `Z(K) ⊓ ker ψ` is
trivial. -/
theorem card_center_inf_ker_eq_one {K T : Type*} [Group K] [Group T] [Finite K]
    (hZ : Nat.card (Subgroup.center K) = 2) {z : K} (hz : z ∈ Subgroup.center K)
    {ψ : K →* T} (h1 : ψ z ≠ 1) :
    Nat.card (Subgroup.center K ⊓ ψ.ker : Subgroup K) = 1 := by
  have hdvd2 : Nat.card (Subgroup.center K ⊓ ψ.ker : Subgroup K) ∣ 2 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left (a := Subgroup.center K) (b := ψ.ker))
    rwa [hZ] at h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · exact h
  · exfalso
    have heq : Subgroup.center K ⊓ ψ.ker = Subgroup.center K :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZ, h])
    have hzk : z ∈ Subgroup.center K ⊓ ψ.ker := heq.ge hz
    exact h1 (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hzk).2)

/-- The element `(1, x²)` (i.e. `inr (ofAdd 2)`) is central in `Dic₃ = ℤ/3 ⋊ ℤ/4`. -/
theorem dic3_central_mem :
    (SemidirectProduct.inr (Multiplicative.ofAdd (2 : ZMod 4)) : fourP_III 3) ∈
      Subgroup.center (fourP_III 3) := by
  rw [mem_center_semidirectProduct_iff
    (fun k hk n hn => fpf_mulAut_multiplicative_zmod 3 _ hk n hn)
    ⟨Multiplicative.ofAdd (1 : ZMod 4), by
      change unitAutHom ((-1 : (ZMod 3)ˣ) ^ (1 : ZMod 4).val) ≠ 1
      exact unitAutHom_ne_one (by decide)⟩]
  refine ⟨rfl, Subgroup.mem_center_iff.mpr fun g => mul_comm g _, ?_⟩
  change unitAutHom ((-1 : (ZMod 3)ˣ) ^ (2 : ZMod 4).val) = 1
  rw [(by decide : ((-1 : (ZMod 3)ˣ) ^ (2 : ZMod 4).val) = 1), map_one]

theorem dic3_central_ne_one :
    (SemidirectProduct.inr (Multiplicative.ofAdd (2 : ZMod 4)) : fourP_III 3) ≠ 1 := by
  intro h
  have h2 := congrArg SemidirectProduct.right h
  simp only [SemidirectProduct.right_inr, SemidirectProduct.one_right] at h2
  exact absurd h2 (by decide)

theorem card_center_fourP_V_three : Nat.card (Subgroup.center (fourP_V 3)) = 2 := by
  rw [card_center_prod, card_center_eq_card_of_comm _ mul_comm, card_mult_zmod_two,
    DihedralGroup.center_eq_bot_of_odd_ne_one (by decide) (by norm_num), Subgroup.card_bot]

/-- The element `(1, 1)` (nontrivial in the `ℤ/2` factor) is central in `ℤ/2 × D₆`. -/
theorem fourP_V_central_mem :
    ((Multiplicative.ofAdd (1 : ZMod 2), 1) : fourP_V 3) ∈ Subgroup.center (fourP_V 3) := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Prod.ext_iff.mpr ⟨mul_comm _ _, by simp⟩

theorem fourP_V_central_ne_one :
    ((Multiplicative.ofAdd (1 : ZMod 2), 1) : fourP_V 3) ≠ 1 := by
  intro h
  exact absurd (congrArg Prod.fst h) (by decide)

/-- Evaluating `dic3ActionHom` on the `ℤ/4`-part of `Dic₃`. -/
theorem dic3ActionHom_inr_apply (c : (ZMod 5)ˣ) (hc : c ^ (4 : ℕ) = 1)
    (x : Multiplicative (ZMod 4)) :
    dic3ActionHom c hc (SemidirectProduct.inr x)
      = unitAutHom (c ^ (Multiplicative.toAdd x).val) := by
  simp only [dic3ActionHom, MonoidHom.comp_apply, SemidirectProduct.lift_inr]
  rfl

/-- The range of the `ℤ/2`-factor action has exactly the two automorphisms `{1, inv}`. -/
theorem card_range_prodZMod2ActionHom_cInv {H : Type*} [Group H] :
    Nat.card (prodZMod2ActionHom (H := H) cInv cInv_pow_two).range = 2 := by
  have hr : (prodZMod2ActionHom (H := H) cInv cInv_pow_two).range =
      (unitAutHom.comp (powHom cInv cInv_pow_two)).range :=
    range_comp_of_surjective _ (fun a => ⟨(a, 1), rfl⟩)
  rw [hr, card_range_comp_of_injective (powHom cInv cInv_pow_two) unitAutHom_injective,
    range_powHom_eq_zpowers (by norm_num) cInv cInv_pow_two, Nat.card_zpowers, orderOf_cInv]

theorem card_center_sixtyRep_II_inv : Nat.card (Subgroup.center sixtyRep_II_inv) = 6 := by
  change Nat.card (Subgroup.center (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_II 3)
    (prodZMod2ActionHom cInv cInv_pow_two))) = 6
  rw [card_center_semidirectProduct_of_fpf
    (fun k hk n hn => fpf_mulAut_multiplicative_zmod 5 _ hk n hn)
    ⟨(Multiplicative.ofAdd (1 : ZMod 2), 1), by
      change unitAutHom (cInv ^ (1 : ZMod 2).val) ≠ 1
      exact unitAutHom_ne_one (by decide)⟩]
  have hcenter : Subgroup.center (fourP_II 3) = ⊤ := by
    ext x
    simp only [Subgroup.mem_center_iff, Subgroup.mem_top, iff_true]
    exact fun g => mul_comm g x
  rw [hcenter, top_inf_eq]
  have h1 := card_ker_mul_card_range
    (prodZMod2ActionHom (H := Multiplicative (ZMod (2 * 3))) cInv cInv_pow_two)
  have h2 : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod (2 * 3))) = 12 := by
    rw [Nat.card_prod, card_mult_zmod_two, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  rw [h2, card_range_prodZMod2ActionHom_cInv] at h1
  omega

theorem card_center_sixtyRep_III_inv : Nat.card (Subgroup.center sixtyRep_III_inv) = 2 := by
  change Nat.card (Subgroup.center (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_III 3)
    (dic3ActionHom cInv cInv_pow_four))) = 2
  rw [card_center_semidirectProduct_of_fpf
    (fun k hk n hn => fpf_mulAut_multiplicative_zmod 5 _ hk n hn)
    ⟨SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4)), by
      rw [dic3ActionHom_inr_apply]
      exact unitAutHom_ne_one (by decide)⟩]
  refine card_center_inf_ker_eq_two card_center_fourP_III_three dic3_central_mem
    dic3_central_ne_one ?_
  rw [dic3ActionHom_inr_apply,
    (by decide : cInv ^ (Multiplicative.toAdd (Multiplicative.ofAdd (2 : ZMod 4))).val = 1),
    map_one]

theorem card_center_sixtyRep_III_faithful :
    Nat.card (Subgroup.center sixtyRep_III_faithful) = 1 := by
  change Nat.card (Subgroup.center (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_III 3)
    (dic3ActionHom cFaithful cFaithful_pow_four))) = 1
  rw [card_center_semidirectProduct_of_fpf
    (fun k hk n hn => fpf_mulAut_multiplicative_zmod 5 _ hk n hn)
    ⟨SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4)), by
      rw [dic3ActionHom_inr_apply]
      exact unitAutHom_ne_one (by decide)⟩]
  refine card_center_inf_ker_eq_one card_center_fourP_III_three dic3_central_mem ?_
  rw [dic3ActionHom_inr_apply]
  exact unitAutHom_ne_one (by decide)

theorem card_center_sixtyRep_V_inv : Nat.card (Subgroup.center sixtyRep_V_inv) = 1 := by
  change Nat.card (Subgroup.center (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_V 3)
    (prodZMod2ActionHom cInv cInv_pow_two))) = 1
  rw [card_center_semidirectProduct_of_fpf
    (fun k hk n hn => fpf_mulAut_multiplicative_zmod 5 _ hk n hn)
    ⟨(Multiplicative.ofAdd (1 : ZMod 2), 1), by
      change unitAutHom (cInv ^ (1 : ZMod 2).val) ≠ 1
      exact unitAutHom_ne_one (by decide)⟩]
  refine card_center_inf_ker_eq_one card_center_fourP_V_three fourP_V_central_mem ?_
  change unitAutHom (cInv ^ (1 : ZMod 2).val) ≠ 1
  exact unitAutHom_ne_one (by decide)

theorem card_center_sixtyRep_V_sign : Nat.card (Subgroup.center sixtyRep_V_sign) = 2 := by
  change Nat.card (Subgroup.center (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_V 3)
    prodD6SignActionHom)) = 2
  rw [card_center_semidirectProduct_of_fpf
    (fun k hk n hn => fpf_mulAut_multiplicative_zmod 5 _ hk n hn)
    ⟨(1, DihedralGroup.sr 0), by
      change unitAutHom cInv ≠ 1
      exact unitAutHom_ne_one cInv_ne_one⟩]
  refine card_center_inf_ker_eq_two card_center_fourP_V_three fourP_V_central_mem
    fourP_V_central_ne_one ?_
  change unitAutHom (d6SignUnitHom 1) = 1
  rw [map_one, map_one]

theorem card_center_alternating_five :
    Nat.card (Subgroup.center (alternatingGroup (Fin 5))) = 1 := by
  rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num), Subgroup.card_bot]

/-! ### Order-4 elements: splitting the remaining center ties

The pairs `(I_inv, II_inv)` (centers `6`), `(III_inv, V_sign)` (centers `2`) and
`(III_faithful, V_inv, A₅)` (centers `1`) share center cardinality. An order-`4` element of
`ℤ/5 ⋊ K` must project to an order-`4` element of `K` (since `|ℤ/5| = 5` is odd), so the
representatives over `ℤ/12` and `Dic₃` have one while those over `ℤ/2 × ℤ/6` and `ℤ/2 × D₆`
do not; `A₅` is handled by simplicity. -/

/-- In `ℤ/5 ⋊[φ] K`, an element of order `4` projects to an element of order `4` in `K`. -/
theorem right_orderOf_four {K : Type*} [Group K] [Finite K]
    {φ : K →* MulAut (Multiplicative (ZMod 5))}
    (g : SemidirectProduct (Multiplicative (ZMod 5)) K φ) (hg : orderOf g = 4) :
    orderOf (SemidirectProduct.rightHom g) = 4 := by
  have hdvd : orderOf (SemidirectProduct.rightHom g) ∣ 4 := by
    have h := orderOf_map_dvd SemidirectProduct.rightHom g
    rwa [hg] at h
  by_contra hne
  have h2 : orderOf (SemidirectProduct.rightHom g) ∣ 2 := by
    have key : ∀ n ∈ Nat.divisors 4, n ≠ 4 → n ∣ 2 := by decide
    exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hne
  have hpow : SemidirectProduct.rightHom (g ^ 2) = 1 := by
    rw [map_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  have hginl : g ^ 2 = SemidirectProduct.inl ((g ^ 2).left) := by
    apply SemidirectProduct.ext
    · rfl
    · rw [SemidirectProduct.right_inl]
      exact hpow
  have hord2 : orderOf (g ^ 2) = 2 := by
    rw [orderOf_pow, hg]
    decide
  have hdvd5 : orderOf ((g ^ 2).left) ∣ 5 := by
    have h := orderOf_dvd_natCard ((g ^ 2).left)
    rwa [card_mult_zmod_five] at h
  rw [hginl, orderOf_injective (SemidirectProduct.inl : Multiplicative (ZMod 5) →* _)
    SemidirectProduct.inl_injective] at hord2
  rw [hord2] at hdvd5
  norm_num at hdvd5

theorem fourP_II_three_no_order4 : ∀ k : fourP_II 3, orderOf k ≠ 4 := by
  rintro ⟨b, c⟩ h
  rw [Prod.orderOf_mk] at h
  have hb : orderOf b ∣ 2 := by
    have hh := orderOf_dvd_natCard b; rwa [card_mult_zmod_two] at hh
  have hc : orderOf c ∣ 6 := by
    have hcard : Nat.card (Multiplicative (ZMod (2 * 3))) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have hh := orderOf_dvd_natCard c; rwa [hcard] at hh
  have hbnd : Nat.lcm (orderOf b) (orderOf c) ∣ Nat.lcm 2 6 :=
    Nat.lcm_dvd (hb.trans (Nat.dvd_lcm_left 2 6)) (hc.trans (Nat.dvd_lcm_right 2 6))
  rw [h] at hbnd
  norm_num at hbnd

theorem sixtyRep_I_inv_has_order4 : ∃ g : sixtyRep_I_inv, orderOf g = 4 := by
  have hg12 : orderOf (Multiplicative.ofAdd (1 : ZMod 12)) = 12 := by
    rw [orderOf_ofAdd_eq_addOrderOf]; exact ZMod.addOrderOf_one 12
  refine ⟨SemidirectProduct.inr ((Multiplicative.ofAdd (1 : ZMod 12)) ^ 3), ?_⟩
  rw [orderOf_injective (SemidirectProduct.inr : Multiplicative (ZMod 12) →* _)
    SemidirectProduct.inr_injective, orderOf_pow, hg12]
  norm_num

theorem sixtyRep_III_inv_has_order4 : ∃ g : sixtyRep_III_inv, orderOf g = 4 := by
  obtain ⟨k, hk⟩ := fourP_III_3_has_order4
  exact ⟨SemidirectProduct.inr k, by
    rw [orderOf_injective (SemidirectProduct.inr : fourP_III 3 →* _)
      SemidirectProduct.inr_injective, hk]⟩

theorem sixtyRep_III_faithful_has_order4 : ∃ g : sixtyRep_III_faithful, orderOf g = 4 := by
  obtain ⟨k, hk⟩ := fourP_III_3_has_order4
  exact ⟨SemidirectProduct.inr k, by
    rw [orderOf_injective (SemidirectProduct.inr : fourP_III 3 →* _)
      SemidirectProduct.inr_injective, hk]⟩

theorem sixtyRep_II_inv_no_order4 : ∀ g : sixtyRep_II_inv, orderOf g ≠ 4 := fun g hg =>
  fourP_II_three_no_order4 _ (right_orderOf_four g hg)

theorem sixtyRep_V_inv_no_order4 : ∀ g : sixtyRep_V_inv, orderOf g ≠ 4 := fun g hg =>
  fourP_V_three_no_order4 _ (right_orderOf_four g hg)

theorem sixtyRep_V_sign_no_order4 : ∀ g : sixtyRep_V_sign, orderOf g ≠ 4 := fun g hg =>
  fourP_V_three_no_order4 _ (right_orderOf_four g hg)

/-! ### Ruling out `A₅`: simplicity against the normal `ℤ/5` -/

/-- The kernel of `rightHom : N ⋊[φ] K →* K` has the size of `N`. -/
theorem card_ker_rightHom_semidirect {N K : Type*} [Group N] [Group K] {φ : K →* MulAut N} :
    Nat.card ((SemidirectProduct.rightHom : SemidirectProduct N K φ →* K).ker) = Nat.card N := by
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective SemidirectProduct.inl_injective, Subgroup.card_top]

/-- A group with a normal subgroup of order `5` is not isomorphic to the simple group `A₅`. -/
theorem not_mulEquiv_alternating_five_of_normal_five {A : Type*} [Group A]
    (H : Subgroup A) [hn : H.Normal] (hH : Nat.card H = 5) :
    ¬ Nonempty (A ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  have hnormal : (H.map e.toMonoidHom).Normal := hn.map e.toMonoidHom e.surjective
  have hcard : Nat.card (H.map e.toMonoidHom) = 5 := by
    rw [Subgroup.card_map_of_injective e.injective, hH]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.map e.toMonoidHom) hnormal with hbot | htop
  · rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  · rw [htop, Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin] at hcard
    exact absurd hcard (by decide)

theorem sixtyRep_III_faithful_ne_A5 :
    ¬ Nonempty (sixtyRep_III_faithful ≃* alternatingGroup (Fin 5)) := by
  refine not_mulEquiv_alternating_five_of_normal_five (SemidirectProduct.rightHom).ker ?_
  rw [card_ker_rightHom_semidirect, card_mult_zmod_five]

theorem sixtyRep_V_inv_ne_A5 : ¬ Nonempty (sixtyRep_V_inv ≃* alternatingGroup (Fin 5)) := by
  refine not_mulEquiv_alternating_five_of_normal_five (SemidirectProduct.rightHom).ker ?_
  rw [card_ker_rightHom_semidirect, card_mult_zmod_five]

/-! ### The remaining tied pairs and the bundled distinctness -/

theorem sixtyRep_I_inv_ne_II_inv : ¬ Nonempty (sixtyRep_I_inv ≃* sixtyRep_II_inv) :=
  not_mulEquiv_of_orderOf sixtyRep_I_inv_has_order4 sixtyRep_II_inv_no_order4

theorem sixtyRep_III_inv_ne_V_sign : ¬ Nonempty (sixtyRep_III_inv ≃* sixtyRep_V_sign) :=
  not_mulEquiv_of_orderOf sixtyRep_III_inv_has_order4 sixtyRep_V_sign_no_order4

theorem sixtyRep_III_faithful_ne_V_inv : ¬ Nonempty (sixtyRep_III_faithful ≃* sixtyRep_V_inv) :=
  not_mulEquiv_of_orderOf sixtyRep_III_faithful_has_order4 sixtyRep_V_inv_no_order4

/-- The thirteen representatives of the isomorphism classes of groups of order `60`. -/
noncomputable def sixtyReps : Fin 13 → Type
  | 0 => sixtyRep_I
  | 1 => sixtyRep_II
  | 2 => sixtyRep_III
  | 3 => sixtyRep_V
  | 4 => sixtyRep_A4
  | 5 => sixtyRep_I_inv
  | 6 => sixtyRep_I_faithful
  | 7 => sixtyRep_II_inv
  | 8 => sixtyRep_III_inv
  | 9 => sixtyRep_III_faithful
  | 10 => sixtyRep_V_inv
  | 11 => sixtyRep_V_sign
  | 12 => alternatingGroup (Fin 5)

noncomputable instance instGroupSixtyReps : ∀ i, Group (sixtyReps i)
  | 0 => inferInstanceAs (Group sixtyRep_I)
  | 1 => inferInstanceAs (Group sixtyRep_II)
  | 2 => inferInstanceAs (Group sixtyRep_III)
  | 3 => inferInstanceAs (Group sixtyRep_V)
  | 4 => inferInstanceAs (Group sixtyRep_A4)
  | 5 => inferInstanceAs (Group sixtyRep_I_inv)
  | 6 => inferInstanceAs (Group sixtyRep_I_faithful)
  | 7 => inferInstanceAs (Group sixtyRep_II_inv)
  | 8 => inferInstanceAs (Group sixtyRep_III_inv)
  | 9 => inferInstanceAs (Group sixtyRep_III_faithful)
  | 10 => inferInstanceAs (Group sixtyRep_V_inv)
  | 11 => inferInstanceAs (Group sixtyRep_V_sign)
  | 12 => inferInstanceAs (Group (alternatingGroup (Fin 5)))

/-- **Distinctness.** The thirteen representatives of order `60` are pairwise non-isomorphic:
partition by center cardinality (`60, 60, 10, 10, 5, 6, 3, 6, 2, 1, 1, 2, 1`), then split the
tied pairs by the existence of an order-`4` element or (against `A₅`) by simplicity. -/
theorem sixtyReps_pairwiseNonMulEquiv : PairwiseNonMulEquiv sixtyReps := by
  apply PairwiseNonMulEquiv.of_center_card
    (cs := fun i => match i with
      | 0 => 60 | 1 => 60 | 2 => 10 | 3 => 10 | 4 => 5 | 5 => 6 | 6 => 3
      | 7 => 6 | 8 => 2 | 9 => 1 | 10 => 1 | 11 => 2 | 12 => 1)
  · intro i
    fin_cases i
    · exact card_center_sixtyRep_I
    · exact card_center_sixtyRep_II
    · exact card_center_sixtyRep_III
    · exact card_center_sixtyRep_V
    · exact card_center_sixtyRep_A4
    · exact card_center_sixtyRep_I_inv
    · exact card_center_sixtyRep_I_faithful
    · exact card_center_sixtyRep_II_inv
    · exact card_center_sixtyRep_III_inv
    · exact card_center_sixtyRep_III_faithful
    · exact card_center_sixtyRep_V_inv
    · exact card_center_sixtyRep_V_sign
    · exact card_center_alternating_five
  · intro i j hcs hiso
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hcs (by decide)
        | exact absurd hiso sixtyRep_I_ne_II
        | exact absurd hiso sixtyRep_III_ne_V
        | exact absurd hiso sixtyRep_I_inv_ne_II_inv
        | exact absurd hiso sixtyRep_III_inv_ne_V_sign
        | exact absurd hiso sixtyRep_III_faithful_ne_V_inv
        | exact absurd hiso sixtyRep_III_faithful_ne_A5
        | exact absurd hiso sixtyRep_V_inv_ne_A5
        | exact absurd (Nonempty.intro hiso.some.symm) sixtyRep_I_ne_II
        | exact absurd (Nonempty.intro hiso.some.symm) sixtyRep_III_ne_V
        | exact absurd (Nonempty.intro hiso.some.symm) sixtyRep_I_inv_ne_II_inv
        | exact absurd (Nonempty.intro hiso.some.symm) sixtyRep_III_inv_ne_V_sign
        | exact absurd (Nonempty.intro hiso.some.symm) sixtyRep_III_faithful_ne_V_inv
        | exact absurd (Nonempty.intro hiso.some.symm) sixtyRep_III_faithful_ne_A5
        | exact absurd (Nonempty.intro hiso.some.symm) sixtyRep_V_inv_ne_A5

/-! ### Pinning the action: `K = ℤ/12` (cyclic)

Every action `φ' : ℤ/12 →* Aut(ℤ/5)` factors through `unitAutHom` as `unitAutHom ∘ ψ`, and `ψ` is
determined by a single unit `c = ψ(generator)` with `c¹² = 1`. Since `(ZMod 5)ˣ` is cyclic of
order `4`, `c ∈ {1, cInv, cFaithful, cFaithful⁻¹}`; the last case is moved to `cFaithful` by
precomposing with the inversion automorphism of `ℤ/12` (valid since `ℤ/12` is abelian). -/

/-- A trivial-action semidirect product is the direct product. -/
noncomputable def semidirectProductTrivial (N K : Type*) [Group N] [Group K] :
    SemidirectProduct N K (1 : K →* MulAut N) ≃* N × K :=
  { toEquiv := SemidirectProduct.equivProd
    map_mul' := fun x y => by
      rcases x with ⟨n₁, h₁⟩
      rcases y with ⟨n₂, h₂⟩
      simp }

/-- Every action of `K` on `Multiplicative (ZMod p)` (`p` prime) factors through `unitAutHom`. -/
theorem exists_unitAutHom_comp_eq {K : Type*} [Group K] {p : ℕ} [Fact p.Prime]
    (φ' : K →* MulAut (Multiplicative (ZMod p))) :
    ∃ ψ : K →* (ZMod p)ˣ, φ' = unitAutHom.comp ψ := by
  choose f hf using fun k => exists_unitAutHom_eq (φ' k)
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    apply unitAutHom_injective
    rw [map_mul, ← hf, ← hf, ← hf, map_mul]
  exact ⟨MonoidHom.mk' f hmul, MonoidHom.ext fun k => hf k⟩

/-- The generator `ofAdd 1` of `Multiplicative (ZMod n)` raised to the `.val` power of any
element recovers that element. -/
theorem ofAdd_one_pow_val {n : ℕ} [NeZero n] (x : Multiplicative (ZMod n)) :
    (Multiplicative.ofAdd (1 : ZMod n)) ^ (Multiplicative.toAdd x).val = x := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  exact ofAdd_toAdd x

/-- A homomorphism out of a cyclic `Multiplicative (ZMod q)` sending the generator to `c` is
`powHom c hc`. -/
theorem eq_powHom_of_hom_apply {q p : ℕ} [NeZero q] (ψ : Multiplicative (ZMod q) →* (ZMod p)ˣ)
    (c : (ZMod p)ˣ) (h1 : ψ (Multiplicative.ofAdd 1) = c) (hc : c ^ q = 1) :
    ψ = powHom c hc := by
  refine MonoidHom.ext fun x => ?_
  conv_lhs => rw [← ofAdd_one_pow_val x, map_pow, h1]
  rfl

/-- Composing `powHom c hc` with the inversion automorphism of `Multiplicative (ZMod q)` gives
`powHom c⁻¹ hc'`. -/
theorem powHom_comp_inv {q p : ℕ} [NeZero q] (c : (ZMod p)ˣ) (hc : c ^ q = 1)
    (hc' : c⁻¹ ^ q = 1) :
    (powHom c hc).comp (MulEquiv.inv (Multiplicative (ZMod q))).toMonoidHom = powHom c⁻¹ hc' := by
  refine MonoidHom.ext fun x => ?_
  change powHom c hc (x⁻¹) = powHom c⁻¹ hc' x
  have h1 : powHom c hc (x⁻¹) = (powHom c hc x)⁻¹ := map_inv (powHom c hc) x
  rw [h1]
  change (c ^ (Multiplicative.toAdd x).val)⁻¹ = c⁻¹ ^ (Multiplicative.toAdd x).val
  exact (inv_pow c _).symm

/-- The fourth unit of `(ZMod 5)ˣ`, `cFaithful⁻¹ = 3`. Kept as an explicit literal (rather than
`cFaithful⁻¹`) since `decide` does not reduce through the `Units` inverse operation. -/
def cThird : (ZMod 5)ˣ := ZMod.unitOfCoprime 3 (by decide)

theorem cFaithful_mul_cThird : cFaithful * cThird = 1 := by decide

theorem cThird_eq_cFaithful_inv : cThird = cFaithful⁻¹ :=
  eq_inv_of_mul_eq_one_right cFaithful_mul_cThird

theorem cThird_pow_twelve : cThird ^ (12 : ℕ) = 1 := by decide

/-- **Exhaustiveness for `K = ℤ/12`.** Every action of `ℤ/12` on `ℤ/5` gives a semidirect product
isomorphic to `sixtyRep_I`, `sixtyRep_I_inv`, or `sixtyRep_I_faithful`. -/
theorem sixty_classify_fourP_I (φ' : fourP_I 3 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_I 3) φ' ≃* sixtyRep_I) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_I 3) φ' ≃* sixtyRep_I_inv) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_I 3) φ' ≃*
      sixtyRep_I_faithful) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  have hclass : ∀ c : (ZMod 5)ˣ, c = 1 ∨ c = cInv ∨ c = cFaithful ∨ c = cThird := by decide
  have hcases : ψ (Multiplicative.ofAdd 1) = 1 ∨ ψ (Multiplicative.ofAdd 1) = cInv ∨
      ψ (Multiplicative.ofAdd 1) = cFaithful ∨ ψ (Multiplicative.ofAdd 1) = cThird :=
    hclass _
  rcases hcases with h1 | h1 | h1 | h1
  · left
    have hcone : (1 : (ZMod 5)ˣ) ^ (12 : ℕ) = 1 := one_pow 12
    have hψeq : ψ = powHom 1 hcone := eq_powHom_of_hom_apply ψ 1 h1 hcone
    have heq1 : unitAutHom.comp (powHom (1 : (ZMod 5)ˣ) hcone) =
        (1 : fourP_I 3 →* MulAut (Multiplicative (ZMod 5))) := by
      refine MonoidHom.ext fun x => ?_
      change unitAutHom (powHom (1 : (ZMod 5)ˣ) hcone x) = 1
      rw [show powHom (1 : (ZMod 5)ˣ) hcone x = 1 from by
        change (1 : (ZMod 5)ˣ) ^ (Multiplicative.toAdd x).val = 1
        exact one_pow _, map_one]
    have hφ'1 : φ' = (1 : fourP_I 3 →* MulAut (Multiplicative (ZMod 5))) := by
      rw [hψ, hψeq, heq1]
    rw [hφ'1]
    exact ⟨(semidirectProductCongr_eq rfl).trans (semidirectProductTrivial _ _)⟩
  · right; left
    have hψeq : ψ = powHom cInv cInv_pow_twelve := eq_powHom_of_hom_apply ψ cInv h1 cInv_pow_twelve
    have hφ'1 : φ' = actionHom cInv cInv_pow_twelve := by rw [hψ, hψeq, actionHom]
    rw [hφ'1]
    exact ⟨semidirectProductCongr_eq rfl⟩
  · right; right
    have hψeq : ψ = powHom cFaithful cFaithful_pow_twelve :=
      eq_powHom_of_hom_apply ψ cFaithful h1 cFaithful_pow_twelve
    have hφ'1 : φ' = actionHom cFaithful cFaithful_pow_twelve := by rw [hψ, hψeq, actionHom]
    rw [hφ'1]
    exact ⟨semidirectProductCongr_eq rfl⟩
  · right; right
    have hψeq : ψ = powHom cThird cThird_pow_twelve := eq_powHom_of_hom_apply ψ cThird h1
      cThird_pow_twelve
    have hc' : (cFaithful⁻¹ : (ZMod 5)ˣ) ^ (12 : ℕ) = 1
    := cThird_eq_cFaithful_inv ▸ cThird_pow_twelve
    have step1 := powHom_comp_inv cFaithful cFaithful_pow_twelve hc'
    have step2 : powHom cFaithful⁻¹ hc' = powHom cThird cThird_pow_twelve := by
      refine MonoidHom.ext fun x => ?_
      change cFaithful⁻¹ ^ (Multiplicative.toAdd x).val = cThird ^ (Multiplicative.toAdd x).val
      rw [← cThird_eq_cFaithful_inv]
    have hcomp : (actionHom cFaithful cFaithful_pow_twelve).comp
        (MulEquiv.inv (Multiplicative (ZMod 12))).toMonoidHom =
        unitAutHom.comp (powHom cThird cThird_pow_twelve) := by
      change unitAutHom.comp ((powHom cFaithful cFaithful_pow_twelve).comp
        (MulEquiv.inv (Multiplicative (ZMod 12))).toMonoidHom) = _
      rw [step1, step2]
    have hφ'1 : φ' = (actionHom cFaithful cFaithful_pow_twelve).comp
        (MulEquiv.inv (Multiplicative (ZMod 12))).toMonoidHom := by
      rw [hcomp, ← hψeq, ← hψ]
    rw [hφ'1]
    exact ⟨(semidirectProductCongr_eq rfl).trans (semidirectProductCongrAut _)⟩

/-! ### Pinning the action: `K = A₄`

`A₄` is generated by its three-cycles (`alternatingGroup.closure_isThreeCycles_eq_top`), each of
order `3`. Since `(ZMod 5)ˣ` has order `4` (coprime to `3`), any homomorphism `A₄ →* (ZMod 5)ˣ`
kills every three-cycle, hence is trivial. -/

theorem card_zmod5_units : Nat.card (ZMod 5)ˣ = 4 := by rw [Nat.card_eq_fintype_card]; decide

/-- Any homomorphism from `A₄` to `(ZMod 5)ˣ` is trivial. -/
theorem hom_fourP_A4_eq_one (ψ : fourP_A4 →* (ZMod 5)ˣ) : ψ = 1 := by
  have hthree : ∀ g : fourP_A4, Equiv.Perm.IsThreeCycle (g : Equiv.Perm (Fin 4)) → ψ g = 1 := by
    intro g hg
    have hg3 : g ^ 3 = 1 := by
      have hord : orderOf g = 3 := by
        rw [← orderOf_injective (alternatingGroup (Fin 4)).subtype Subtype.coe_injective]
        exact hg.orderOf
      rw [← hord]; exact pow_orderOf_eq_one g
    have h3 : (ψ g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    have h4 : (ψ g) ^ 4 = 1 := by
      have hdvd := orderOf_dvd_natCard (ψ g)
      rw [card_zmod5_units] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have heq : (ψ g) ^ (3 + 1) = ψ g := by rw [pow_succ, h3, one_mul]
    rw [← heq]
    exact h4
  have hle : (Subgroup.closure {g : fourP_A4 | Equiv.Perm.IsThreeCycle (g : Equiv.Perm (Fin 4))})
      ≤ ψ.ker := by
    rw [Subgroup.closure_le]
    exact fun g hg => MonoidHom.mem_ker.mpr (hthree g hg)
  rw [alternatingGroup.closure_isThreeCycles_eq_top] at hle
  exact MonoidHom.ext fun g => MonoidHom.mem_ker.mp (hle (Subgroup.mem_top g))

/-- **Exhaustiveness for `K = A₄`.** The only action of `A₄` on `ℤ/5` is trivial. -/
theorem sixty_classify_fourP_A4 (φ' : fourP_A4 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) fourP_A4 φ' ≃* sixtyRep_A4) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  have hψ1 : ψ = 1 := hom_fourP_A4_eq_one ψ
  have hφ'1 : φ' = (1 : fourP_A4 →* MulAut (Multiplicative (ZMod 5))) := by
    rw [hψ, hψ1, MonoidHom.comp_one]
  rw [hφ'1]
  exact ⟨(semidirectProductCongr_eq rfl).trans (semidirectProductTrivial _ _)⟩

/-! ### Pinning the action: `K = ℤ/2 × ℤ/6`

`Hom(K, Aut(ℤ/5))` has four elements, parametrised by `(c₁, c₂) ∈ {1, cInv}²` (the images of the
two generators). `(1,1)` is trivial; the other three collapse to a single `Aut(K)`-orbit (matching
the "three index-`2` subgroups, permuted transitively" fact from `Order60.Semiproduct`). The orbit
is witnessed by two commuting-coordinate *shears* `S₁ (a,b) = (a·ρ(b), b)` and
`S₂ (a,b) = (a, b·ι(a)⁻¹)` (`ρ : ℤ/6 → ℤ/2` reduction, `ι : ℤ/2 → ℤ/6` the order-`2` lift
`1 ↦ 3`), each visibly an involution; their composite `S₁ ∘ S₂ ∘ S₁` realises the "swap" that
exchanges `a` with the mod-`2` part of `b`. -/

/-- Reduction mod `2` on `ZMod 6` (as a hom of the multiplicative avatars). -/
noncomputable def rho26 : Multiplicative (ZMod 6) →* Multiplicative (ZMod 2) :=
  ((ZMod.castHom (show (2 : ℕ) ∣ 6 from by norm_num) (ZMod 2)).toAddMonoidHom).toMultiplicative

/-- The order-`2` lift `1 ↦ 3` from `ZMod 2` into `ZMod 6`. -/
noncomputable def iota26 : Multiplicative (ZMod 2) →* Multiplicative (ZMod 6) :=
  (AddMonoidHom.mk' (fun x : ZMod 2 => (3 : ZMod 6) * (x.val : ZMod 6))
    (by decide)).toMultiplicative

theorem rho26_one : rho26 (1 : Multiplicative (ZMod 6)) = 1 := map_one rho26

theorem rho26_iota26 : ∀ x : Multiplicative (ZMod 2), rho26 (iota26 x) = x := by decide

theorem sq_eq_one_zmod2 : ∀ y : Multiplicative (ZMod 2), y * y = 1 := by decide

theorem sq_eq_one_iota26 : ∀ x : Multiplicative (ZMod 2), iota26 x * iota26 x = 1 := by decide

/-- The **shear** `(a, b) ↦ (a · ρ(b), b)` of `ℤ/2 × ℤ/6`, an involution since `ρ(b)² = 1`. -/
noncomputable def sixtyShearS1 : fourP_II 3 ≃* fourP_II 3 :=
  { toFun := fun p => (p.1 * rho26 p.2, p.2)
    invFun := fun p => (p.1 * rho26 p.2, p.2)
    left_inv := fun p => by
      change (p.1 * rho26 p.2 * rho26 p.2, p.2) = p
      rw [mul_assoc, sq_eq_one_zmod2, mul_one]
    right_inv := fun p => by
      change (p.1 * rho26 p.2 * rho26 p.2, p.2) = p
      rw [mul_assoc, sq_eq_one_zmod2, mul_one]
    map_mul' := fun p q => by
      change (p.1 * q.1 * rho26 (p.2 * q.2), p.2 * q.2) =
        (p.1 * rho26 p.2 * (q.1 * rho26 q.2), p.2 * q.2)
      rw [map_mul]
      exact Prod.ext (by ac_rfl) rfl}

/-- The **shear** `(a, b) ↦ (a, b · ι(a)⁻¹)` of `ℤ/2 × ℤ/6`, an involution since `ι(a)² = 1`. -/
noncomputable def sixtyShearS2 : fourP_II 3 ≃* fourP_II 3 :=
  { toFun := fun p => (p.1, p.2 * (iota26 p.1)⁻¹)
    invFun := fun p => (p.1, p.2 * (iota26 p.1)⁻¹)
    left_inv := fun p => by
      change (p.1, p.2 * (iota26 p.1)⁻¹ * (iota26 p.1)⁻¹) = p
      have h1 : (iota26 p.1)⁻¹ * (iota26 p.1)⁻¹ = 1 := by
        rw [← mul_inv_rev]; exact inv_eq_one.mpr (sq_eq_one_iota26 p.1)
      rw [mul_assoc, h1, mul_one]
    right_inv := fun p => by
      change (p.1, p.2 * (iota26 p.1)⁻¹ * (iota26 p.1)⁻¹) = p
      have h1 : (iota26 p.1)⁻¹ * (iota26 p.1)⁻¹ = 1 := by
        rw [← mul_inv_rev]; exact inv_eq_one.mpr (sq_eq_one_iota26 p.1)
      rw [mul_assoc, h1, mul_one]
    map_mul' := fun p q => by
      change (p.1 * q.1, p.2 * q.2 * (iota26 (p.1 * q.1))⁻¹) =
        (p.1, p.2 * (iota26 p.1)⁻¹) * (q.1, q.2 * (iota26 q.1)⁻¹)
      refine Prod.ext rfl ?_
      change p.2 * q.2 * (iota26 (p.1 * q.1))⁻¹ = p.2 * (iota26 p.1)⁻¹ * (q.2 * (iota26 q.1)⁻¹)
      rw [map_mul, mul_inv_rev]
      ac_rfl}

/-- The **swap** automorphism `S₁ ∘ S₂ ∘ S₁`, exchanging `a` with the mod-`2` part of `b`. -/
noncomputable def sixtySwapII : fourP_II 3 ≃* fourP_II 3 :=
  sixtyShearS1.trans (sixtyShearS2.trans sixtyShearS1)

theorem sixtySwapII_apply (p : fourP_II 3) :
    sixtySwapII p = sixtyShearS1 (sixtyShearS2 (sixtyShearS1 p)) := rfl

theorem rho26_ofAdd_one : rho26 (Multiplicative.ofAdd (1 : ZMod 6))
= Multiplicative.ofAdd (1 : ZMod 2) := by
  decide

theorem inv_ofAdd_one_zmod2 : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by
  decide


theorem cInv_pow_six : cInv ^ (6 : ℕ) = 1 := by decide

/-- **Exhaustiveness for `K = ℤ/2 × ℤ/6`.** Every action of `ℤ/2 × ℤ/6` on `ℤ/5` gives a
semidirect product isomorphic to `sixtyRep_II` or `sixtyRep_II_inv`. -/
theorem sixty_classify_fourP_II (φ' : fourP_II 3 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_II 3) φ' ≃* sixtyRep_II) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_II 3) φ' ≃*
      sixtyRep_II_inv) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  set e1 : fourP_II 3 := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  set e2 : fourP_II 3 := (1, Multiplicative.ofAdd (1 : ZMod 6))
  have hext : ∀ f g : fourP_II 3 →* (ZMod 5)ˣ, f e1 = g e1 → f e2 = g e2 → f = g := by
    intro f g h1 h2
    refine MonoidHom.ext fun x => ?_
    have hx : x = e1 ^ (Multiplicative.toAdd x.1).val * e2 ^ (Multiplicative.toAdd x.2).val := by
      apply Prod.ext
      · change x.1 = (e1 ^ (Multiplicative.toAdd x.1).val).1
        * (e2 ^ (Multiplicative.toAdd x.2).val).1
        rw [Prod.pow_fst, Prod.pow_fst, one_pow, mul_one, ofAdd_one_pow_val]
      · change x.2 = (e1 ^ (Multiplicative.toAdd x.1).val).2
        * (e2 ^ (Multiplicative.toAdd x.2).val).2
        rw [Prod.pow_snd, Prod.pow_snd, one_pow, one_mul, ofAdd_one_pow_val]
    rw [hx, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h1, h2]
  have he1_sq : e1 ^ 2 = 1 := by decide
  have he2_six : e2 ^ 6 = 1 := by decide
  have hpsi1_2 : (ψ e1) ^ 2 = 1 := by rw [← map_pow, he1_sq, map_one]
  have hpsi2_4 : (ψ e2) ^ 4 = 1 := by
    have hdvd := orderOf_dvd_natCard (ψ e2)
    rw [card_zmod5_units] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hpsi2_6 : (ψ e2) ^ 6 = 1 := by rw [← map_pow, he2_six, map_one]
  have hpsi2_2 : (ψ e2) ^ 2 = 1 := by
    have hsplit : (ψ e2) ^ (4 + 2) = (ψ e2) ^ 4 * (ψ e2) ^ 2 := pow_add (ψ e2) 4 2
    rw [show (4 + 2 : ℕ) = 6 from rfl, hpsi2_6, hpsi2_4] at hsplit
    exact (one_mul _).symm.trans hsplit.symm
  have hclass2 : ∀ c : (ZMod 5)ˣ, c ^ 2 = 1 → c = 1 ∨ c = cInv := by decide
  rcases hclass2 (ψ e1) hpsi1_2 with h1 | h1 <;> rcases hclass2 (ψ e2) hpsi2_2 with h2 | h2
  · -- (1,1): trivial
    left
    have hψ1 : ψ = 1 := by
      apply hext
      · rw [h1]; rfl
      · rw [h2]; rfl
    have hφ'1 : φ' = (1 : fourP_II 3 →* MulAut (Multiplicative (ZMod 5))) := by
      rw [hψ, hψ1, MonoidHom.comp_one]
    rw [hφ'1]
    exact ⟨(semidirectProductCongr_eq rfl).trans (semidirectProductTrivial _ _)⟩
  · -- (1, cInv): pure second-factor action, transform via the swap
    right
    have hswap_e1 : (sixtySwapII e1).1 = 1 := by
      rw [sixtySwapII_apply]
      show (sixtyShearS1 (sixtyShearS2 (sixtyShearS1 e1))).1 = 1
      have hs1 : sixtyShearS1 e1 = e1 := by
        change (e1.1 * rho26 e1.2, e1.2) = e1
        change (Multiplicative.ofAdd (1 : ZMod 2) * rho26 (1 : Multiplicative (ZMod 6)),
          (1 : Multiplicative (ZMod 6))) = e1
        rw [rho26_one, mul_one]
      rw [hs1]
      have hs2 : sixtyShearS2 e1 = (Multiplicative.ofAdd (1 : ZMod 2),
          (iota26 (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹) := by
        change (e1.1, e1.2 * (iota26 e1.1)⁻¹) = _
        change (Multiplicative.ofAdd (1 : ZMod 2),
          (1 : Multiplicative (ZMod 6)) * (iota26 (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹) = _
        rw [one_mul]
      rw [hs2]
      change Multiplicative.ofAdd (1 : ZMod 2) *
          rho26 (iota26 (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹ = 1
      rw [map_inv, rho26_iota26, inv_ofAdd_one_zmod2]
      exact sq_eq_one_zmod2 _
    have hswap_e2 : (sixtySwapII e2).1 = Multiplicative.ofAdd (1 : ZMod 2) := by
      rw [sixtySwapII_apply]
      show (sixtyShearS1 (sixtyShearS2 (sixtyShearS1 e2))).1 = Multiplicative.ofAdd 1
      have hs1 : sixtyShearS1 e2 =
          (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 6)) := by
        change (e2.1 * rho26 e2.2, e2.2) = _
        change ((1 : Multiplicative (ZMod 2)) * rho26 (Multiplicative.ofAdd (1 : ZMod 6)),
          Multiplicative.ofAdd (1 : ZMod 6)) = _
        rw [rho26_ofAdd_one, one_mul]
      rw [hs1]
      have hs2 : sixtyShearS2 (Multiplicative.ofAdd (1 : ZMod 2),
      Multiplicative.ofAdd (1 : ZMod 6)) =
          (Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (1 : ZMod 6) *
            (iota26 (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹) := rfl
      rw [hs2]
      change Multiplicative.ofAdd (1 : ZMod 2) *
        rho26 (Multiplicative.ofAdd (1 : ZMod 6) * (iota26 (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹) =
        Multiplicative.ofAdd (1 : ZMod 2)
      rw [map_mul, map_inv, rho26_ofAdd_one, rho26_iota26, inv_ofAdd_one_zmod2]
      have h2eq : (Multiplicative.ofAdd (1 : ZMod 2)) * (Multiplicative.ofAdd (1 : ZMod 2) *
          Multiplicative.ofAdd (1 : ZMod 2)) = Multiplicative.ofAdd (1 : ZMod 2) := by
        rw [sq_eq_one_zmod2, mul_one]
      exact h2eq
    have hψswap : ψ = ((powHom cInv cInv_pow_two).comp
        (MonoidHom.fst (Multiplicative (ZMod 2)) (Multiplicative (ZMod 6)))).comp
        sixtySwapII.toMonoidHom := by
      apply hext
      · change ψ e1 = (powHom cInv cInv_pow_two) ((sixtySwapII e1).1)
        rw [h1, hswap_e1]
        change (1 : (ZMod 5)ˣ) = cInv ^ (Multiplicative.toAdd (1 : Multiplicative (ZMod 2))).val
        simp
      · change ψ e2 = (powHom cInv cInv_pow_two) ((sixtySwapII e2).1)
        rw [h2, hswap_e2]
        change cInv = cInv ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val
        rw [toAdd_ofAdd, ZMod.val_one, pow_one]
    have hφ'eq : φ' = ((prodZMod2ActionHom (H := Multiplicative (ZMod 6)) cInv cInv_pow_two)).comp
        sixtySwapII.toMonoidHom := by
      rw [hψ, hψswap, prodZMod2ActionHom]
      rfl
    rw [hφ'eq]
    exact ⟨semidirectProductCongrAut sixtySwapII⟩
  · -- (cInv, 1): direct match to sixtyRep_II_inv
    right
    have hψeq : ψ = (powHom cInv cInv_pow_two).comp (MonoidHom.fst (Multiplicative (ZMod 2))
        (Multiplicative (ZMod 6))) := by
      apply hext
      · rw [h1]
        change cInv = cInv ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val
        rw [toAdd_ofAdd, ZMod.val_one, pow_one]
      · rw [h2]
        change (1 : (ZMod 5)ˣ) = cInv ^ (Multiplicative.toAdd (1 : Multiplicative (ZMod 2))).val
        simp
    have hφ'eq : φ' = prodZMod2ActionHom (H := Multiplicative (ZMod 6)) cInv cInv_pow_two := by
      rw [hψ, hψeq, prodZMod2ActionHom, MonoidHom.comp_assoc]
    rw [hφ'eq]
    exact ⟨semidirectProductCongr_eq rfl⟩
  · -- (cInv, cInv): transform via the shear S₁
    right
    have hshear_e1 : (sixtyShearS1 e1).1 = Multiplicative.ofAdd (1 : ZMod 2) := by
      change (e1.1 * rho26 e1.2, e1.2).1 = Multiplicative.ofAdd 1
      change Multiplicative.ofAdd (1 : ZMod 2) * rho26 (1 : Multiplicative (ZMod 6)) =
        Multiplicative.ofAdd 1
      rw [rho26_one, mul_one]
    have hshear_e2 : (sixtyShearS1 e2).1 = Multiplicative.ofAdd (1 : ZMod 2) := by
      change (e2.1 * rho26 e2.2, e2.2).1 = Multiplicative.ofAdd 1
      change (1 : Multiplicative (ZMod 2)) * rho26 (Multiplicative.ofAdd (1 : ZMod 6)) =
        Multiplicative.ofAdd 1
      rw [rho26_ofAdd_one, one_mul]
    have hψshear : ψ = ((powHom cInv cInv_pow_two).comp
        (MonoidHom.fst (Multiplicative (ZMod 2)) (Multiplicative (ZMod 6)))).comp
        sixtyShearS1.toMonoidHom := by
      apply hext
      · change ψ e1 = (powHom cInv cInv_pow_two) ((sixtyShearS1 e1).1)
        rw [h1, hshear_e1]
        change cInv = cInv ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val
        rw [toAdd_ofAdd, ZMod.val_one, pow_one]
      · change ψ e2 = (powHom cInv cInv_pow_two) ((sixtyShearS1 e2).1)
        rw [h2, hshear_e2]
        change cInv = cInv ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val
        rw [toAdd_ofAdd, ZMod.val_one, pow_one]
    have hφ'eq : φ' = ((prodZMod2ActionHom (H := Multiplicative (ZMod 6)) cInv cInv_pow_two)).comp
        sixtyShearS1.toMonoidHom := by
      rw [hψ, hψshear, prodZMod2ActionHom]
      rfl
    rw [hφ'eq]
    exact ⟨semidirectProductCongrAut sixtyShearS1⟩

/-! ### Pinning the action: `K = Dic₃`

`Dic₃ = ℤ/3 ⋊[-1] ℤ/4` has abelianization `ℤ/4` (the `ℤ/3` part is killed by any homomorphism to
an abelian group of order coprime to `3`), so `Hom(Dic₃, Aut(ℤ/5))` is again parametrised by a
unit `c` with `c⁴ = 1`: exactly `dic3ActionHom c hc`. As for `K = ℤ/12`, `c` and `c⁻¹` give
isomorphic semidirect products, via the automorphism `(n, h) ↦ (n, h⁻¹)` of `Dic₃` (valid because
the defining action of `Dic₃` has order `≤ 2`, so `unitAutHom`'s image commutes with inversion). -/

/-- The action `actionHom (-1 : (ZMod 3)ˣ) hc` defining `Dic₃` has order `≤ 2` on every element:
`(-1)² = 1` in any commutative ring, so this holds before even applying `unitAutHom`. -/
theorem dic3_defining_action_sq (h : Multiplicative (ZMod 4)) :
    (actionHom (-1 : (ZMod 3)ˣ) (by decide : (-1 : (ZMod 3)ˣ) ^ 4 = 1) h) ^ 2 = 1 := by
  rw [actionHom, MonoidHom.comp_apply, ← map_pow]
  have : (powHom (-1 : (ZMod 3)ˣ) (by decide : (-1 : (ZMod 3)ˣ) ^ 4 = 1) h) ^ 2 =
      ((-1 : (ZMod 3)ˣ) ^ 2) ^ (Multiplicative.toAdd h).val := by
    change ((-1 : (ZMod 3)ˣ) ^ (Multiplicative.toAdd h).val) ^ 2 = _
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [this]
  have h2 : (-1 : (ZMod 3)ˣ) ^ 2 = 1 := by decide
  rw [h2, one_pow, map_one]

/-- The automorphism `(n, h) ↦ (n, h⁻¹)` of `Dic₃`, valid since `Dic₃`'s defining action has
order `≤ 2` (so inverting `h` on the right of the semidirect-product formula changes nothing). -/
noncomputable def dic3Invert : fourP_III 3 ≃* fourP_III 3 :=
  { toFun := fun p => ⟨p.left, p.right⁻¹⟩
    invFun := fun p => ⟨p.left, p.right⁻¹⟩
    left_inv := fun p => by simp
    right_inv := fun p => by simp
    map_mul' := fun p q => by
      apply SemidirectProduct.ext
      · change (p * q).left =
          p.left * (actionHom (-1 : (ZMod 3)ˣ) (by decide) p.right⁻¹) q.left
        have hφinv : (actionHom (-1 : (ZMod 3)ˣ) (by decide : (-1 : (ZMod 3)ˣ) ^ 4 = 1) p.right⁻¹)
            = actionHom (-1 : (ZMod 3)ˣ) (by decide) p.right := by
          rw [map_inv]
          exact inv_eq_of_mul_eq_one_left (by
            rw [← sq]; exact dic3_defining_action_sq p.right)
        rw [hφinv]; rfl
      · change (p * q).right⁻¹ = p.right⁻¹ * q.right⁻¹
        change (p.right * q.right)⁻¹ = p.right⁻¹ * q.right⁻¹
        rw [mul_inv_rev, mul_comm] }

theorem dic3Invert_apply (p : fourP_III 3) : dic3Invert p = ⟨p.left, p.right⁻¹⟩ := rfl

theorem card_mult_zmod_three : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem dic3_inl_order3 (n : Multiplicative (ZMod 3)) :
    (SemidirectProduct.inl n : fourP_III 3) ^ 3 = 1 := by
  have hn3 : n ^ 3 = 1 := by
    have hdvd := orderOf_dvd_natCard n
    rw [card_mult_zmod_three] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  rw [← map_pow, hn3, map_one]

/-- Every homomorphism `ψ : Dic₃ →* (ZMod 5)ˣ` killing the `ℤ/3`-part, sending the `ℤ/4`-generator
to `c` (with `c⁴ = 1`), determines the action `dic3ActionHom c hc`. -/
theorem eq_dic3ActionHom_of_hom (ψ : fourP_III 3 →* (ZMod 5)ˣ)
    (hψinl : ∀ n : Multiplicative (ZMod 3), ψ (SemidirectProduct.inl n) = 1)
    (c : (ZMod 5)ˣ) (hc4 : c ^ (4 : ℕ) = 1)
    (h1 : ψ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))) = c) :
    unitAutHom.comp ψ = dic3ActionHom c hc4 := by
  rw [dic3ActionHom]
  congr 1
  refine MonoidHom.ext fun x => ?_
  have hx : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
    SemidirectProduct.mk_eq_inl_mul_inr x.right x.left
  rw [hx]
  simp only [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr, hψinl, one_mul,
    MonoidHom.one_apply]
  have hψinr : ψ.comp SemidirectProduct.inr = powHom c hc4 :=
    eq_powHom_of_hom_apply (ψ.comp SemidirectProduct.inr) c h1 hc4
  exact congrFun (congrArg DFunLike.coe hψinr) x.right

/-- **Exhaustiveness for `K = Dic₃`.** Every action of `Dic₃` on `ℤ/5` gives a semidirect product
isomorphic to `sixtyRep_III`, `sixtyRep_III_inv`, or `sixtyRep_III_faithful`. -/
theorem sixty_classify_fourP_III (φ' : fourP_III 3 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_III 3) φ' ≃* sixtyRep_III) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_III 3) φ' ≃*
      sixtyRep_III_inv) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_III 3) φ' ≃*
      sixtyRep_III_faithful) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  have hψinl : ∀ n : Multiplicative (ZMod 3), ψ (SemidirectProduct.inl n) = 1 := by
    intro n
    have h3 : (ψ (SemidirectProduct.inl n)) ^ 3 = 1 := by
      rw [← map_pow, dic3_inl_order3, map_one]
    have h4 : (ψ (SemidirectProduct.inl n)) ^ 4 = 1 := by
      have hdvd := orderOf_dvd_natCard (ψ (SemidirectProduct.inl n))
      rw [card_zmod5_units] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have heq : (ψ (SemidirectProduct.inl n)) ^ (3 + 1) = ψ (SemidirectProduct.inl n) := by
      rw [pow_succ, h3, one_mul]
    rw [← heq]; exact h4
  have hc4 : (ψ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4)))) ^ (4 : ℕ) = 1 := by
    have hg4 : (Multiplicative.ofAdd (1 : ZMod 4)) ^ (4 : ℕ) = 1 := by
      have hord : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 := by
        rw [orderOf_ofAdd_eq_addOrderOf]; exact ZMod.addOrderOf_one 4
      have hp := pow_orderOf_eq_one (Multiplicative.ofAdd (1 : ZMod 4))
      rwa [hord] at hp
    have hg4' : (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4)) :
    fourP_III 3) ^ (4 : ℕ) = 1 := by
      rw [← map_pow, hg4, map_one]
    rw [← map_pow, hg4', map_one]
  have hclass : ψ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))) = 1 ∨
      ψ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))) = cInv ∨
      ψ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))) = cFaithful ∨
      ψ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 4))) = cThird := by
    have h : ∀ c : (ZMod 5)ˣ, c = 1 ∨ c = cInv ∨ c = cFaithful ∨ c = cThird := by decide
    exact h _
  rcases hclass with h1 | h1 | h1 | h1
  · left
    have hφ'eq : φ' = dic3ActionHom 1 (one_pow 4) := by
      rw [hψ]; exact eq_dic3ActionHom_of_hom ψ hψinl 1 (one_pow 4) h1
    have hone : dic3ActionHom (1 : (ZMod 5)ˣ) (one_pow 4) =
        (1 : fourP_III 3 →* MulAut (Multiplicative (ZMod 5))) := by
      rw [dic3ActionHom]
      refine MonoidHom.ext fun x => ?_
      have hx : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
        SemidirectProduct.mk_eq_inl_mul_inr x.right x.left
      rw [hx]
      simp only [MonoidHom.comp_apply, map_mul, SemidirectProduct.lift_inl,
        SemidirectProduct.lift_inr, MonoidHom.one_apply, map_one, one_mul]
      change unitAutHom ((1 : (ZMod 5)ˣ) ^ (Multiplicative.toAdd x.right).val) = 1
      rw [one_pow, map_one]
    rw [hφ'eq, hone]
    exact ⟨(semidirectProductCongr_eq rfl).trans (semidirectProductTrivial _ _)⟩
  · right; left
    have hφ'eq : φ' = dic3ActionHom cInv cInv_pow_four := by
      rw [hψ]; exact eq_dic3ActionHom_of_hom ψ hψinl cInv cInv_pow_four h1
    rw [hφ'eq]
    exact ⟨semidirectProductCongr_eq rfl⟩
  · right; right
    have hφ'eq : φ' = dic3ActionHom cFaithful cFaithful_pow_four := by
      rw [hψ]; exact eq_dic3ActionHom_of_hom ψ hψinl cFaithful cFaithful_pow_four h1
    rw [hφ'eq]
    exact ⟨semidirectProductCongr_eq rfl⟩
  · right; right
    have hc' : (cFaithful⁻¹ : (ZMod 5)ˣ) ^ (4 : ℕ) = 1
    := by rw [inv_pow, cFaithful_pow_four, inv_one]
    have hφ'eq : φ' = dic3ActionHom cThird (cThird_eq_cFaithful_inv ▸ hc') := by
      rw [hψ]; exact eq_dic3ActionHom_of_hom ψ hψinl cThird (cThird_eq_cFaithful_inv ▸ hc') h1
    have hcomp : (dic3ActionHom cFaithful cFaithful_pow_four).comp dic3Invert.toMonoidHom =
        dic3ActionHom cThird (cThird_eq_cFaithful_inv ▸ hc') := by
      refine MonoidHom.ext fun x => ?_
      change dic3ActionHom cFaithful cFaithful_pow_four (dic3Invert x) =
        dic3ActionHom cThird (cThird_eq_cFaithful_inv ▸ hc') x
      rw [dic3Invert_apply]
      have hxr : (⟨x.left, x.right⁻¹⟩ : fourP_III 3) =
          SemidirectProduct.inl x.left * SemidirectProduct.inr x.right⁻¹ :=
        SemidirectProduct.mk_eq_inl_mul_inr x.right⁻¹ x.left
      have hx : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
        SemidirectProduct.mk_eq_inl_mul_inr x.right x.left
      change unitAutHom (SemidirectProduct.lift 1 (powHom cFaithful cFaithful_pow_four) _
          (⟨x.left, x.right⁻¹⟩ : fourP_III 3)) =
        unitAutHom (SemidirectProduct.lift 1 (powHom cThird (cThird_eq_cFaithful_inv ▸ hc')) _ x)
      conv_rhs => rw [hx]
      rw [hxr]
      simp only [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
      congr 1
      refine congrArg unitAutHom ?_
      rw [map_inv]
      have : (powHom cFaithful cFaithful_pow_four x.right)⁻¹ =
          powHom cFaithful⁻¹ hc' x.right := by
        change (cFaithful ^ (Multiplicative.toAdd x.right).val)⁻¹ =
          cFaithful⁻¹ ^ (Multiplicative.toAdd x.right).val
        exact (inv_pow cFaithful _).symm
      rw [this]
      exact congrFun (congrArg DFunLike.coe
        (show powHom cFaithful⁻¹ hc' = powHom cThird (cThird_eq_cFaithful_inv ▸ hc') from by
          refine MonoidHom.ext fun y => ?_
          change cFaithful⁻¹ ^ (Multiplicative.toAdd y).val = cThird ^ (Multiplicative.toAdd y).val
          rw [← cThird_eq_cFaithful_inv])) x.right
    rw [hφ'eq, ← hcomp]
    exact ⟨(semidirectProductCongr_eq rfl).trans (semidirectProductCongrAut dic3Invert)⟩


/-! ### Pinning the action: `K = ℤ/2 × D₆`

`Hom(K, Aut(ℤ/5))` has four elements, parametrised by `(c₁, c₂) ∈ {1, cInv}²`: `c₁` is the image
of the `ℤ/2`-generator, and `c₂` is the image of a reflection (rotations are killed, since they
have order dividing `3`, coprime to `4`, and all reflections have the same image since they differ
by a rotation). `(1,1)` is trivial (`sixtyRep_V`); `(cInv,1)` matches `sixtyRep_V_inv`; `(1,cInv)`
matches `sixtyRep_V_sign`; `(cInv,cInv)` collapses to `(cInv,1)` via the shear automorphism
`(a, g) ↦ (a · χ(g), g)`, where `χ : D₆ → ℤ/2` is the sign character. -/

/-- The sign character `D₆ →* ℤ/2` (as the multiplicative avatar): rotations trivial, reflections
to the generator. -/
def d6SignZMod2Hom : DihedralGroup 3 →* Multiplicative (ZMod 2) where
  toFun
    | DihedralGroup.r _ => 1
    | DihedralGroup.sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · rfl
    · simp [DihedralGroup.r_mul_sr]
    · simp [DihedralGroup.sr_mul_r]
    · simp only [DihedralGroup.sr_mul_sr]
      decide

theorem d6SignZMod2Hom_r (i : ZMod 3) : d6SignZMod2Hom (DihedralGroup.r i) = 1 := rfl

theorem d6SignZMod2Hom_one : d6SignZMod2Hom (1 : DihedralGroup 3) = 1 := rfl

theorem d6SignZMod2Hom_sr (i : ZMod 3) :
    d6SignZMod2Hom (DihedralGroup.sr i) = Multiplicative.ofAdd 1 := rfl

/-- The **shear** `(a, g) ↦ (a · χ(g), g)` of `ℤ/2 × D₆`, an involution since `χ(g)² = 1`. -/
noncomputable def sixtyShearV : fourP_V 3 ≃* fourP_V 3 :=
  { toFun := fun p => (p.1 * d6SignZMod2Hom p.2, p.2)
    invFun := fun p => (p.1 * d6SignZMod2Hom p.2, p.2)
    left_inv := fun p => by
      change (p.1 * d6SignZMod2Hom p.2 * d6SignZMod2Hom p.2, p.2) = p
      rw [mul_assoc, sq_eq_one_zmod2, mul_one]
    right_inv := fun p => by
      change (p.1 * d6SignZMod2Hom p.2 * d6SignZMod2Hom p.2, p.2) = p
      rw [mul_assoc, sq_eq_one_zmod2, mul_one]
    map_mul' := fun p q => by
      change (p.1 * q.1 * d6SignZMod2Hom (p.2 * q.2), p.2 * q.2) =
        (p.1 * d6SignZMod2Hom p.2 * (q.1 * d6SignZMod2Hom q.2), p.2 * q.2)
      rw [map_mul]
      exact Prod.ext (by ac_rfl) rfl }

theorem sixtyShearV_apply (p : fourP_V 3) :
    sixtyShearV p = (p.1 * d6SignZMod2Hom p.2, p.2) := rfl

theorem dihedral3_r_order_dvd_three (i : ZMod 3) :
(DihedralGroup.r i : DihedralGroup 3) ^ 3 = 1 := by
  have hdvd : orderOf (DihedralGroup.r i : DihedralGroup 3) ∣ 3 := by
    rw [DihedralGroup.orderOf_r]
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left 3 i.val)
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

/-- **Exhaustiveness for `K = ℤ/2 × D₆`.** Every action of `ℤ/2 × D₆` on `ℤ/5` gives a semidirect
product isomorphic to `sixtyRep_V`, `sixtyRep_V_inv`, or `sixtyRep_V_sign`. -/
theorem sixty_classify_fourP_V (φ' : fourP_V 3 →* MulAut (Multiplicative (ZMod 5))) :
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_V 3) φ' ≃* sixtyRep_V) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_V 3) φ' ≃* sixtyRep_V_inv) ∨
    Nonempty (SemidirectProduct (Multiplicative (ZMod 5)) (fourP_V 3) φ' ≃*
      sixtyRep_V_sign) := by
  obtain ⟨ψ, hψ⟩ := exists_unitAutHom_comp_eq φ'
  set e1 : fourP_V 3 := (Multiplicative.ofAdd (1 : ZMod 2), 1)
  have hψrot : ∀ i : ZMod 3, ψ (1, DihedralGroup.r i) = 1 := by
    intro i
    have h3 : (ψ (1, DihedralGroup.r i)) ^ 3 = 1 := by
      have hrot3 : ((1, DihedralGroup.r i) : fourP_V 3) ^ 3 = 1 :=
        Prod.ext (one_pow 3) (dihedral3_r_order_dvd_three i)
      rw [← map_pow, hrot3, map_one]
    have h4 : (ψ (1, DihedralGroup.r i)) ^ 4 = 1 := by
      have hdvd := orderOf_dvd_natCard (ψ (1, DihedralGroup.r i))
      rw [card_zmod5_units] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have heq : (ψ (1, DihedralGroup.r i)) ^ (3 + 1) = ψ (1, DihedralGroup.r i) := by
      rw [pow_succ, h3, one_mul]
    rw [← heq]; exact h4
  have hext : ∀ f g : fourP_V 3 →* (ZMod 5)ˣ,
      f e1 = g e1 → f (1, DihedralGroup.sr 0) = g (1, DihedralGroup.sr 0) →
      (∀ i : ZMod 3, f (1, DihedralGroup.r i) = 1) →
      (∀ i : ZMod 3, g (1, DihedralGroup.r i) = 1) → f = g := by
    intro f g h1 h2 hfrot hgrot
    refine MonoidHom.ext fun x => ?_
    obtain ⟨a, dg⟩ := x
    have hae : (a, (1 : DihedralGroup 3)) = e1 ^ (Multiplicative.toAdd a).val := by
      apply Prod.ext
      · change a = (Multiplicative.ofAdd (1 : ZMod 2)) ^ (Multiplicative.toAdd a).val
        exact (ofAdd_one_pow_val a).symm
      · change (1 : DihedralGroup 3) = (1 : DihedralGroup 3) ^ (Multiplicative.toAdd a).val
        rw [one_pow]
    rcases dg with i | i
    · have hx : (a, DihedralGroup.r i) = ((a, (1 : DihedralGroup 3))) * (1, DihedralGroup.r i) :=
        Prod.ext (mul_one a).symm (one_mul _).symm
      rw [hx, map_mul, map_mul, hfrot, hgrot, mul_one, mul_one, hae, map_pow, map_pow, h1]
    · have hsri : (DihedralGroup.sr i : DihedralGroup 3)
      = DihedralGroup.sr 0 * DihedralGroup.r i := by
        rw [DihedralGroup.sr_mul_r]; congr 1; rw [zero_add]
      have hx : (a, DihedralGroup.sr i) =
          ((a, (1 : DihedralGroup 3))) * ((1, DihedralGroup.sr 0) * (1, DihedralGroup.r i)) := by
        apply Prod.ext
        · change a = a * (1 * 1)
          rw [mul_one, mul_one]
        · change DihedralGroup.sr i = 1 * (DihedralGroup.sr 0 * DihedralGroup.r i)
          rw [one_mul, ← hsri]
      rw [hx, map_mul, map_mul, map_mul, map_mul, hfrot, hgrot, mul_one, mul_one, hae, map_pow,
        map_pow, h1, h2]
  have he1_sq : e1 ^ 2 = 1 := by decide
  have hsr0_sq : ((1, DihedralGroup.sr 0) : fourP_V 3) ^ 2 = 1 :=
    Prod.ext (one_pow 2) (by rw [sq]; exact DihedralGroup.sr_mul_self 0)
  have hpsi1_2 : (ψ e1) ^ 2 = 1 := by rw [← map_pow, he1_sq, map_one]
  have hpsi2_2 : (ψ (1, DihedralGroup.sr 0)) ^ 2 = 1 := by rw [← map_pow, hsr0_sq, map_one]
  have hclass2 : ∀ c : (ZMod 5)ˣ, c ^ 2 = 1 → c = 1 ∨ c = cInv := by decide
  rcases hclass2 (ψ e1) hpsi1_2 with h1 | h1 <;>
    rcases hclass2 (ψ (1, DihedralGroup.sr 0)) hpsi2_2 with h2 | h2
  · -- (1,1): trivial
    left
    have hψ1 : ψ = 1 := by
      apply hext
      · rw [h1]; rfl
      · rw [h2]; rfl
      · exact hψrot
      · intro i; rfl
    have hφ'1 : φ' = (1 : fourP_V 3 →* MulAut (Multiplicative (ZMod 5))) := by
      rw [hψ, hψ1, MonoidHom.comp_one]
    rw [hφ'1]
    exact ⟨(semidirectProductCongr_eq rfl).trans (semidirectProductTrivial _ _)⟩
  · -- (1, cInv): pure sign action, matches sixtyRep_V_sign
    right; right
    have hkey : ψ = (powHom cInv cInv_pow_two).comp
        (d6SignZMod2Hom.comp (MonoidHom.snd (Multiplicative (ZMod 2)) (DihedralGroup 3))) := by
      apply hext
      · change ψ e1 = (powHom cInv cInv_pow_two) (d6SignZMod2Hom (1 : DihedralGroup 3))
        rw [h1]
        change (1 : (ZMod 5)ˣ) = powHom cInv cInv_pow_two (1 : Multiplicative (ZMod 2))
        rw [map_one]
      · change ψ (1, DihedralGroup.sr 0)
        = (powHom cInv cInv_pow_two) (d6SignZMod2Hom (DihedralGroup.sr 0))
        rw [h2, d6SignZMod2Hom_sr]
        change cInv = cInv ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val
        rw [toAdd_ofAdd, ZMod.val_one, pow_one]
      · exact hψrot
      · intro i
        change (powHom cInv cInv_pow_two) (d6SignZMod2Hom (DihedralGroup.r i)) = 1
        rw [d6SignZMod2Hom_r, map_one]
    have hbridge : (powHom cInv cInv_pow_two).comp d6SignZMod2Hom = d6SignUnitHom := by
      refine MonoidHom.ext fun g => ?_
      rcases g with i | i
      · rw [MonoidHom.comp_apply, d6SignZMod2Hom_r, map_one]; rfl
      · rw [MonoidHom.comp_apply, d6SignZMod2Hom_sr]
        change cInv ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val =
          d6SignUnitHom (DihedralGroup.sr i)
        rw [toAdd_ofAdd, ZMod.val_one, pow_one]; rfl
    have hφ'eq : φ' = prodD6SignActionHom := by
      rw [hψ, hkey]
      refine MonoidHom.ext fun x => ?_
      change unitAutHom (powHom cInv cInv_pow_two (d6SignZMod2Hom x.2)) = prodD6SignActionHom x
      rw [show powHom cInv cInv_pow_two (d6SignZMod2Hom x.2) = d6SignUnitHom x.2 from
        congrFun (congrArg DFunLike.coe hbridge) x.2]
      rfl
    rw [hφ'eq]
    exact ⟨semidirectProductCongr_eq rfl⟩
  · -- (cInv, 1): pure ZMod2-factor action, matches sixtyRep_V_inv
    right; left
    have hkey : ψ = (powHom cInv cInv_pow_two).comp
        (MonoidHom.fst (Multiplicative (ZMod 2)) (DihedralGroup 3)) := by
      apply hext
      · change ψ e1 = (powHom cInv cInv_pow_two) (Multiplicative.ofAdd (1 : ZMod 2))
        rw [h1]
        change cInv = cInv ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val
        rw [toAdd_ofAdd, ZMod.val_one, pow_one]
      · change ψ (1, DihedralGroup.sr 0) = (powHom cInv cInv_pow_two) (1 : Multiplicative (ZMod 2))
        rw [h2, map_one]
      · exact hψrot
      · intro i
        change (powHom cInv cInv_pow_two) (1 : Multiplicative (ZMod 2)) = 1
        rw [map_one]
    have hφ'eq : φ' = prodZMod2ActionHom (H := DihedralGroup 3) cInv cInv_pow_two := by
      rw [hψ, hkey, prodZMod2ActionHom, MonoidHom.comp_assoc]
    rw [hφ'eq]
    exact ⟨semidirectProductCongr_eq rfl⟩
  · -- (cInv, cInv): transform via the shear
    right; left
    have hshear_e1 : (sixtyShearV e1).1 = Multiplicative.ofAdd (1 : ZMod 2) := by
      rw [sixtyShearV_apply]
      change Multiplicative.ofAdd (1 : ZMod 2) * d6SignZMod2Hom (1 : DihedralGroup 3) =
        Multiplicative.ofAdd 1
      rw [d6SignZMod2Hom_one, mul_one]
    have hshear_sr0 : (sixtyShearV (1, DihedralGroup.sr 0)).1
    = Multiplicative.ofAdd (1 : ZMod 2) := by
      rw [sixtyShearV_apply]
      change (1 : Multiplicative (ZMod 2)) * d6SignZMod2Hom (DihedralGroup.sr 0) =
        Multiplicative.ofAdd 1
      rw [d6SignZMod2Hom_sr, one_mul]
    have hψshear : ψ = ((powHom cInv cInv_pow_two).comp
        (MonoidHom.fst (Multiplicative (ZMod 2)) (DihedralGroup 3))).comp
        sixtyShearV.toMonoidHom := by
      apply hext
      · change ψ e1 = (powHom cInv cInv_pow_two) ((sixtyShearV e1).1)
        rw [h1, hshear_e1]
        change cInv = cInv ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val
        rw [toAdd_ofAdd, ZMod.val_one, pow_one]
      · change ψ (1, DihedralGroup.sr 0) = (powHom cInv cInv_pow_two)
          ((sixtyShearV (1, DihedralGroup.sr 0)).1)
        rw [h2, hshear_sr0]
        change cInv = cInv ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val
        rw [toAdd_ofAdd, ZMod.val_one, pow_one]
      · exact hψrot
      · intro i
        change (powHom cInv cInv_pow_two) ((sixtyShearV (1, DihedralGroup.r i)).1) = 1
        rw [sixtyShearV_apply]
        change (powHom cInv cInv_pow_two)
          ((1 : Multiplicative (ZMod 2)) * d6SignZMod2Hom (DihedralGroup.r i)) = 1
        rw [d6SignZMod2Hom_r, mul_one, map_one]
    have hφ'eq : φ' = ((prodZMod2ActionHom (H := DihedralGroup 3) cInv cInv_pow_two)).comp
        sixtyShearV.toMonoidHom := by
      rw [hψ, hψshear, prodZMod2ActionHom]
      rfl
    rw [hφ'eq]
    exact ⟨semidirectProductCongrAut sixtyShearV⟩

/-! ### Combining: full exhaustiveness for order `60`

Transport a semidirect product `N ⋊[φ] K` along abstract isomorphisms `N ≃* N'` and `K ≃* K'` to a
semidirect product on `N', K'`, then apply the five `sixty_classify_fourP_*` theorems above to pin
the transported action down to one of the twelve named representatives. -/

/-- Transporting automorphisms of `N` to automorphisms of `N'` along `θ : N ≃* N'`, by
conjugation. -/
def mulAutTransport {N N' : Type*} [Group N] [Group N'] (θ : N ≃* N') : MulAut N ≃* MulAut N' where
  toFun σ := (θ.symm.trans σ).trans θ
  invFun σ := (θ.trans σ).trans θ.symm
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp
  map_mul' σ τ := by ext x; simp

/-- Transporting a semidirect product along isomorphisms of both factors. -/
theorem exists_semidirectProductCongr {N K N' K' : Type*} [Group N] [Group K] [Group N'] [Group K']
    (φ : K →* MulAut N) (θ : N ≃* N') (σ : K ≃* K') :
    Nonempty (SemidirectProduct N K φ ≃*
      SemidirectProduct N' K'
        ((mulAutTransport θ).toMonoidHom.comp (φ.comp σ.symm.toMonoidHom))) := by
  refine ⟨semidirectProductCongr θ σ (fun k => ?_)⟩
  ext n
  change θ (φ k n) = (mulAutTransport θ (φ (σ.symm (σ k)))) (θ n)
  rw [σ.symm_apply_apply]
  change θ (φ k n) = θ ((φ k) (θ.symm (θ n)))
  rw [θ.symm_apply_apply]

/-- **Full exhaustiveness.** Every group of order `60` is isomorphic to one of the thirteen named
representatives. -/
theorem sixty_classification {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 60) :
    Nonempty (G ≃* sixtyRep_I) ∨ Nonempty (G ≃* sixtyRep_II) ∨
    Nonempty (G ≃* sixtyRep_III) ∨ Nonempty (G ≃* sixtyRep_V) ∨
    Nonempty (G ≃* sixtyRep_A4) ∨ Nonempty (G ≃* sixtyRep_I_inv) ∨
    Nonempty (G ≃* sixtyRep_I_faithful) ∨ Nonempty (G ≃* sixtyRep_II_inv) ∨
    Nonempty (G ≃* sixtyRep_III_inv) ∨ Nonempty (G ≃* sixtyRep_III_faithful) ∨
    Nonempty (G ≃* sixtyRep_V_inv) ∨ Nonempty (G ≃* sixtyRep_V_sign) ∨
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  rcases order60_structural_classification hG with hA5 | ⟨N, K, φ, hNnormal, hNcard, hKcard, ⟨e⟩⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr hA5
  · haveI : Finite N := Nat.finite_of_card_ne_zero (by rw [hNcard]; norm_num)
    haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
    obtain ⟨θ⟩ := prime_classification (p := 5) (by norm_num) hNcard
    have hK12 : Nat.card K = 12 := hKcard
    rcases fourP_12_classification hK12 with hK | hK | hK | hK | hK
    · obtain ⟨σ⟩ := hK
      obtain ⟨e'⟩ := exists_semidirectProductCongr φ θ σ
      rcases sixty_classify_fourP_I ((mulAutTransport θ).toMonoidHom.comp
          (φ.comp σ.symm.toMonoidHom)) with hC | hC | hC
      · obtain ⟨e''⟩ := hC; exact Or.inl ⟨e.trans (e'.trans e'')⟩
      · obtain ⟨e''⟩ := hC
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e.trans (e'.trans e'')⟩
      · obtain ⟨e''⟩ := hC
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inl ⟨e.trans (e'.trans e'')⟩
    · obtain ⟨σ⟩ := hK
      obtain ⟨e'⟩ := exists_semidirectProductCongr φ θ σ
      rcases sixty_classify_fourP_II ((mulAutTransport θ).toMonoidHom.comp
          (φ.comp σ.symm.toMonoidHom)) with hC | hC
      · obtain ⟨e''⟩ := hC; exact Or.inr <| Or.inl ⟨e.trans (e'.trans e'')⟩
      · obtain ⟨e''⟩ := hC
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inl ⟨e.trans (e'.trans e'')⟩
    · obtain ⟨σ⟩ := hK
      obtain ⟨e'⟩ := exists_semidirectProductCongr φ θ σ
      rcases sixty_classify_fourP_III ((mulAutTransport θ).toMonoidHom.comp
          (φ.comp σ.symm.toMonoidHom)) with hC | hC | hC
      · obtain ⟨e''⟩ := hC; exact Or.inr <| Or.inr <| Or.inl ⟨e.trans (e'.trans e'')⟩
      · obtain ⟨e''⟩ := hC
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inl ⟨e.trans (e'.trans e'')⟩
      · obtain ⟨e''⟩ := hC
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inl ⟨e.trans (e'.trans e'')⟩
    · obtain ⟨σ⟩ := hK
      obtain ⟨e'⟩ := exists_semidirectProductCongr φ θ σ
      rcases sixty_classify_fourP_V ((mulAutTransport θ).toMonoidHom.comp
          (φ.comp σ.symm.toMonoidHom)) with hC | hC | hC
      · obtain ⟨e''⟩ := hC; exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e.trans (e'.trans e'')⟩
      · obtain ⟨e''⟩ := hC
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inl ⟨e.trans (e'.trans e'')⟩
      · obtain ⟨e''⟩ := hC
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e.trans (e'.trans e'')⟩
    · obtain ⟨σ⟩ := hK
      obtain ⟨e'⟩ := exists_semidirectProductCongr φ θ σ
      obtain ⟨e''⟩ := sixty_classify_fourP_A4 ((mulAutTransport θ).toMonoidHom.comp
          (φ.comp σ.symm.toMonoidHom))
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e.trans (e'.trans e'')⟩

/-- **The thirteen representatives form a complete classification of groups of order `60`.**
There are exactly thirteen isomorphism classes of groups of order `60`: the twelve solvable
representatives from `Order60.Semiproduct`, and the simple group `A₅`. -/
theorem sixty_isClassif : IsClassif 60 sixtyReps :=
  isClassif_thirteen sixtyRep_I sixtyRep_II sixtyRep_III sixtyRep_V sixtyRep_A4
    sixtyRep_I_inv sixtyRep_I_faithful sixtyRep_II_inv sixtyRep_III_inv sixtyRep_III_faithful
    sixtyRep_V_inv sixtyRep_V_sign (alternatingGroup (Fin 5))
    card_sixtyRep_I card_sixtyRep_II card_sixtyRep_III card_sixtyRep_V card_sixtyRep_A4
    card_sixtyRep_I_inv card_sixtyRep_I_faithful card_sixtyRep_II_inv card_sixtyRep_III_inv
    card_sixtyRep_III_faithful card_sixtyRep_V_inv card_sixtyRep_V_sign
    (by rw [nat_card_alternatingGroup, Nat.card_fin]; decide)
    (fun X _ hX => by
      haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
      exact sixty_classification hX)
    sixtyReps_pairwiseNonMulEquiv

end Smallgroups.UsefulTheorems
