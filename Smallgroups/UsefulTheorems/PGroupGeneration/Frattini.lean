/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.Frattini
import Smallgroups.UsefulTheorems.PGroupGeneration.PCentralSeries

/-!
# p-group generation: the Frattini subgroup of a p-group

**Burnside's basis theorem**, in the form used by the p-group generation machinery: for a
finite `p`-group,

  `frattini G = ⁅G,G⁆ Gᵖ = pLowerCentralSeries p G 1`

(`frattini_eq_pLowerCentralSeries_one`).  The two inclusions:

* `≥` (`pLowerCentralSeries_one_le_frattini`): every maximal subgroup `M` of a finite
  `p`-group is normal (`normal_of_isCoatom_of_isPGroup`, via the normalizer condition for
  nilpotent groups) of index `p` (`card_quotient_coatom`), so `G ⧸ M ≅ C_p` absorbs all
  commutators and `p`-th powers into `M`.
* `≤` (`frattini_le_pLowerCentralSeries_one`): the quotient `V = G ⧸ ⁅G,G⁆Gᵖ` is
  elementary abelian, and in such a group every `v ≠ 1` avoids a maximal subgroup
  (`exists_isCoatom_notMem_of_pow_eq_one` — the elementary "hyperplane" argument: a
  subgroup maximal among those avoiding `v` is a coatom, because `w ∉ M⟨v⟩` would give
  `v ∈ M⟨w⟩`, and solving `v = m w^k` with `gcd(k, p) = 1` puts `w` back in `M⟨v⟩`);
  pulling the coatom back along the quotient map bounds `frattini G`.

Consequences packaged for later use: `commutator_mem_frattini`, `pow_mem_frattini` — the
Frattini quotient of a finite `p`-group is elementary abelian.  This underlies both the
descendant bookkeeping (a central `z` of order `p` outside `frattini G` splits off a
direct `C_p` factor) and cheap isomorphism invariants (the Frattini rank).
-/

namespace Smallgroups.UsefulTheorems

open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ### Maximal subgroups of a finite p-group -/

/-- Maximal subgroups of a finite `p`-group are normal (via the normalizer condition,
since finite `p`-groups are nilpotent). -/
theorem normal_of_isCoatom_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) {M : Subgroup G} (hM : IsCoatom M) : M.Normal := by
  haveI := Fact.mk hp
  haveI : Group.IsNilpotent G := hG.isNilpotent
  exact Subgroup.NormalizerCondition.normal_of_coatom M
    Group.normalizerCondition_of_isNilpotent hM

/-- Maximal subgroups of a finite `p`-group have index `p`. -/
theorem card_quotient_coatom [Finite G] {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    {M : Subgroup G} (hM : IsCoatom M) : Nat.card (G ⧸ M) = p := by
  haveI := Fact.mk hp
  haveI hMnorm : M.Normal := normal_of_isCoatom_of_isPGroup hp hG hM
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hG.to_quotient M)
  haveI hnt : Nontrivial (G ⧸ M) := by
    obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hM.1)
    exact ⟨⟨(g : G ⧸ M), 1, by rw [ne_eq, QuotientGroup.eq_one_iff]; exact hg⟩⟩
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · rw [pow_zero] at hk
      exact absurd hk (Finite.one_lt_card (α := G ⧸ M)).ne'
    · rw [pow_one] at hk
      exact hk
  · exfalso
    -- Cauchy in the quotient produces a subgroup strictly between `M` and `⊤`
    have hdvd : p ∣ Nat.card (G ⧸ M) := hk ▸ dvd_pow_self p (by omega : k ≠ 0)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G ⧸ M) p hdvd
    have hxbot : Subgroup.zpowers x ≠ ⊥ := by
      intro hbot
      have hx1 : x = 1 := by
        rw [← Subgroup.mem_bot, ← hbot]
        exact Subgroup.mem_zpowers x
      rw [hx1, orderOf_one] at hx
      exact hp.one_lt.ne' hx.symm
    have hxne : Subgroup.zpowers x ≠ ⊤ := by
      intro htop
      have hcard : Nat.card (Subgroup.zpowers x) = p := (Nat.card_zpowers x).trans hx
      rw [htop, Subgroup.card_top, hk] at hcard
      have hlt : p ^ 1 < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
      rw [pow_one] at hlt
      omega
    have h1 : M < (Subgroup.zpowers x).comap (QuotientGroup.mk' M) := by
      rw [lt_iff_le_and_ne]
      constructor
      · intro g hg
        rw [Subgroup.mem_comap]
        have hg1 : QuotientGroup.mk' M g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
        rw [hg1]
        exact Subgroup.one_mem _
      · intro heq2
        apply hxbot
        refine Subgroup.comap_injective (QuotientGroup.mk'_surjective M) ?_
        rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
        exact heq2.symm
    have h2 := hM.2 _ h1
    apply hxne
    have h3 := Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective M) (Subgroup.zpowers x)
    rw [← h3, h2]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M)

/-- A maximal subgroup of a finite `p`-group absorbs all commutators and `p`-th powers:
`P₁ = ⁅G,G⁆Gᵖ ≤ M`. -/
theorem pLowerCentralSeries_one_le_coatom [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) {M : Subgroup G} (hM : IsCoatom M) :
    pLowerCentralSeries p G 1 ≤ M := by
  haveI := Fact.mk hp
  haveI hMn : M.Normal := normal_of_isCoatom_of_isPGroup hp hG hM
  have hq : Nat.card (G ⧸ M) = p := card_quotient_coatom hp hG hM
  have hcomm : ∀ a b : G ⧸ M, a * b = b * a := by
    obtain ⟨x, hgen⟩ := (isCyclic_of_prime_card hq).exists_generator
    intro a b
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen a)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen b)
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  rw [pLowerCentralSeries_succ, pLowerCentralSeries_zero]
  apply sup_le
  · rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [← QuotientGroup.eq_one_iff]
    have h1 : ((⁅g, h⁆ : G) : G ⧸ M) = ⁅(g : G ⧸ M), (h : G ⧸ M)⁆ :=
      map_commutatorElement (QuotientGroup.mk' M) g h
    rw [h1]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)
  · refine pPowSubgroup_le p fun g _ => ?_
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hq]
    exact pow_card_eq_one'

/-- The easy half of Burnside: `⁅G,G⁆Gᵖ ≤ frattini G` for a finite `p`-group. -/
theorem pLowerCentralSeries_one_le_frattini [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) : pLowerCentralSeries p G 1 ≤ frattini G :=
  le_iInf₂ fun _ hM => pLowerCentralSeries_one_le_coatom hp hG hM

/-! ### The hyperplane argument in elementary abelian groups -/

/-- In a finite elementary abelian `p`-group, every `v ≠ 1` avoids some maximal subgroup.
This replaces the linear-algebra "extend to a hyperplane" argument by an elementary one:
take `M` maximal among subgroups avoiding `v`; then `M` is a coatom. -/
theorem exists_isCoatom_notMem_of_pow_eq_one {V : Type*} [CommGroup V] [Finite V]
    {p : ℕ} (hp : p.Prime) (hpow : ∀ a : V, a ^ p = 1) {v : V} (hv : v ≠ 1) :
    ∃ M : Subgroup V, IsCoatom M ∧ v ∉ M := by
  haveI : Finite (Subgroup V) :=
    Finite.of_injective ((↑) : Subgroup V → Set V) SetLike.coe_injective
  obtain ⟨M, -, hMmax⟩ := Finite.exists_le_maximal
    (p := fun M : Subgroup V => v ∉ M) (a := ⊥)
    (by rw [Subgroup.mem_bot]; exact hv)
  have hvM : v ∉ M := hMmax.1
  -- every subgroup strictly above `M` contains `v`
  have habove : ∀ K : Subgroup V, M < K → v ∈ K := by
    intro K hK
    by_contra hvK
    exact hK.ne' (le_antisymm (hMmax.2 hvK hK.le) hK.le)
  -- `M ⟨v⟩ = ⊤`
  have hsup : M ⊔ Subgroup.zpowers v = ⊤ := by
    by_contra hne
    obtain ⟨w, -, hw⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
    have hwM : w ∉ M := fun hwM =>
      hw ((le_sup_left : M ≤ M ⊔ Subgroup.zpowers v) hwM)
    have hvW : v ∈ M ⊔ Subgroup.zpowers w := by
      refine habove _ (lt_of_le_of_ne le_sup_left fun heq3 => hwM ?_)
      rw [heq3]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    obtain ⟨m, hm, z, hz, hmz⟩ := Subgroup.mem_sup.mp hvW
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    by_cases hdvd : (p : ℤ) ∣ k
    · -- `w ^ k = 1`, so `v ∈ M`: contradiction
      have hz1 : z = 1 := by
        rw [← hk]
        obtain ⟨t, rfl⟩ := hdvd
        rw [zpow_mul, zpow_natCast, hpow w, one_zpow]
      rw [hz1, mul_one] at hmz
      exact hvM (hmz ▸ hm)
    · -- `gcd (k, p) = 1`, so `w ∈ M ⟨v⟩`: contradiction
      exfalso
      apply hw
      have hnd : ¬ p ∣ k.natAbs := fun hd => hdvd (by
        rwa [← Int.natAbs_natCast p, Int.natAbs_dvd_natAbs] at hd)
      have hgcd : Nat.gcd k.natAbs p = 1 := ((hp.coprime_iff_not_dvd).mpr hnd).symm
      have hwk : w ^ k ∈ M ⊔ Subgroup.zpowers v := by
        have hzeq : z = m⁻¹ * v := by rw [← hmz, inv_mul_cancel_left]
        rw [hk, hzeq]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hm))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
      -- pass to `|k|`, then Bézout
      have hwk' : w ^ ((k.natAbs : ℤ)) ∈ M ⊔ Subgroup.zpowers v := by
        rcases Int.natAbs_eq k with hkk | hkk
        · rw [← hkk]
          exact hwk
        · have hnegk : ((k.natAbs : ℤ)) = -k := by omega
          rw [hnegk, zpow_neg]
          exact Subgroup.inv_mem _ hwk
      have hbez := Nat.gcd_eq_gcd_ab k.natAbs p
      rw [hgcd, Nat.cast_one] at hbez
      have hw1 : w = (w ^ ((k.natAbs : ℤ))) ^ Nat.gcdA k.natAbs p
          * (w ^ ((p : ℤ))) ^ Nat.gcdB k.natAbs p := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add,
          show ((k.natAbs : ℤ)) * Nat.gcdA k.natAbs p
            + (p : ℤ) * Nat.gcdB k.natAbs p = 1 from hbez.symm, zpow_one]
      rw [hw1]
      refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ hwk' _) ?_
      have hwp : w ^ ((p : ℤ)) = 1 := by rw [zpow_natCast, hpow w]
      rw [hwp, one_zpow]
      exact Subgroup.one_mem _
  -- `M` is a coatom
  refine ⟨M, ⟨fun htop => hvM (by rw [htop]; exact Subgroup.mem_top v),
    fun K hK => ?_⟩, hvM⟩
  rw [eq_top_iff, ← hsup]
  exact sup_le hK.le (Subgroup.zpowers_le.mpr (habove K hK))

/-! ### Burnside's basis theorem -/

/-- The hard half of Burnside: `frattini G ≤ ⁅G,G⁆Gᵖ` (this direction needs only
finiteness, not that `G` is a `p`-group). -/
theorem frattini_le_pLowerCentralSeries_one [Finite G] {p : ℕ} (hp : p.Prime) :
    frattini G ≤ pLowerCentralSeries p G 1 := by
  intro x hx
  by_contra hxK
  -- the quotient by `P₁` is elementary abelian
  have hcomm : ∀ a b : G ⧸ pLowerCentralSeries p G 1, a * b = b * a := by
    intro a b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ b
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
      ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact commutator_mem_pLowerCentralSeries_succ (Subgroup.mem_top g) h
  have hpow2 : ∀ a : G ⧸ pLowerCentralSeries p G 1, a ^ p = 1 := by
    intro a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ a
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact pow_mem_pLowerCentralSeries_succ (Subgroup.mem_top g)
  have hv : QuotientGroup.mk' (pLowerCentralSeries p G 1) x ≠ 1 := by
    rw [ne_eq, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hxK
  letI hcg : CommGroup (G ⧸ pLowerCentralSeries p G 1) :=
    { (inferInstance : Group (G ⧸ pLowerCentralSeries p G 1)) with mul_comm := hcomm }
  obtain ⟨Mb, hMb, hvMb⟩ := exists_isCoatom_notMem_of_pow_eq_one hp hpow2 hv
  -- pull the coatom back to `G`
  have hker : (QuotientGroup.mk' (pLowerCentralSeries p G 1)).ker
      ≤ Mb.comap (QuotientGroup.mk' (pLowerCentralSeries p G 1)) := by
    intro g hg
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hg]
    exact Subgroup.one_mem _
  have hcoatom : IsCoatom (Mb.comap (QuotientGroup.mk' (pLowerCentralSeries p G 1))) := by
    constructor
    · intro htop
      apply hMb.1
      rw [← Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective _) Mb, htop]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    · intro X hX
      have hkerX : (QuotientGroup.mk' (pLowerCentralSeries p G 1)).ker ≤ X :=
        le_trans hker hX.le
      have hmapX : X.map (QuotientGroup.mk' (pLowerCentralSeries p G 1)) = ⊤ := by
        refine hMb.2 _ (lt_of_le_of_ne ?_ ?_)
        · rw [← Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective _) Mb]
          exact Subgroup.map_mono hX.le
        · intro heq4
          apply hX.ne
          rw [heq4, Subgroup.comap_map_eq_self hkerX]
      rw [← Subgroup.comap_map_eq_self hkerX, hmapX, Subgroup.comap_top]
  exact hvMb (Subgroup.mem_comap.mp (frattini_le_coatom hcoatom hx))

/-- **Burnside's basis theorem** for finite `p`-groups: the Frattini subgroup is exactly
`⁅G,G⁆ Gᵖ`, the second term of the lower exponent-`p` central series. -/
theorem frattini_eq_pLowerCentralSeries_one [Finite G] {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) : frattini G = pLowerCentralSeries p G 1 :=
  le_antisymm (frattini_le_pLowerCentralSeries_one hp)
    (pLowerCentralSeries_one_le_frattini hp hG)

/-- Commutators lie in the Frattini subgroup of a finite `p`-group: the Frattini quotient
is abelian. -/
theorem commutator_mem_frattini [Finite G] {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (g h : G) : ⁅g, h⁆ ∈ frattini G := by
  rw [frattini_eq_pLowerCentralSeries_one hp hG]
  exact commutator_mem_pLowerCentralSeries_succ (Subgroup.mem_top g) h

/-- `p`-th powers lie in the Frattini subgroup of a finite `p`-group: the Frattini
quotient has exponent `p`. -/
theorem pow_mem_frattini [Finite G] {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (g : G) : g ^ p ∈ frattini G := by
  rw [frattini_eq_pLowerCentralSeries_one hp hG]
  exact pow_mem_pLowerCentralSeries_succ (Subgroup.mem_top g)

/-! ### Cheap isomorphism invariants: the Frattini subgroup

The pieces promised by the module doc above but not previously delivered: `frattini G`
transports exactly along a `MulEquiv` (so `Nat.card (frattini G)` — the "Frattini rank"
data — is a genuine isomorphism invariant), and distributes over direct products. Used
to separate concrete finite `p`-groups that agree on cheaper invariants (element-order
counts, center size) but differ in minimal generator count. -/

/-- The Frattini subgroup transports exactly along a `MulEquiv`: `(frattini G).map e =
frattini H`. An isomorphism of subgroup lattices (`MulEquiv.mapSubgroup`) sends the
radical of one lattice to the radical of the other (`OrderIso.map_radical`), and
`frattini` is literally `Order.radical (Subgroup G)`. -/
theorem frattini_map_eq_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H) :
    (frattini G).map e.toMonoidHom = frattini H :=
  (MulEquiv.mapSubgroup e).map_radical

/-- `Nat.card (frattini G)` — the Frattini rank data — is invariant under `MulEquiv`. -/
theorem frattini_card_eq_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H) :
    Nat.card (frattini G) = Nat.card (frattini H) := by
  rw [← frattini_map_eq_of_mulEquiv e]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv

/-- A direct product of finite `p`-groups is again a finite `p`-group. -/
private theorem isPGroup_prod {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} (hp : p.Prime) (hA : IsPGroup p A) (hB : IsPGroup p B) :
    IsPGroup p (A × B) := by
  haveI := Fact.mk hp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hB
  exact IsPGroup.iff_card.mpr ⟨k + m, by rw [Nat.card_prod, hk, hm, pow_add]⟩

/-- The Frattini subgroup of a direct product of finite `p`-groups is the product of the
individual Frattini subgroups. -/
theorem frattini_prod {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ}
    (hp : p.Prime) (hA : IsPGroup p A) (hB : IsPGroup p B) :
    frattini (A × B) = (frattini A).prod (frattini B) := by
  rw [frattini_eq_pLowerCentralSeries_one hp (isPGroup_prod hp hA hB),
    frattini_eq_pLowerCentralSeries_one hp hA, frattini_eq_pLowerCentralSeries_one hp hB,
    pLowerCentralSeries_prod]

end Smallgroups.UsefulTheorems
