/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.Sylow
import Smallgroups.UsefulTheorems.Order4P_12

/-!
# The four-Sylow-three branch for groups of order 48

This file begins the residual branch `n₃ = 4`, following the conjugation-action
analysis used for the order-`72` residual classification.  The action on the
four Sylow `3`-subgroups embeds its image in `S₄`; its kernel is contained in a
Sylow normalizer.  Cardinal arithmetic reduces the possible kernel orders to
`2`, `4`, `6`, or `12`.
-/

namespace Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-! ### Small Sylow-counting helpers -/

private lemma order48_card_sylow_dvd_of_card_eq_mul
    {H : Type*} [Group H] [Finite H] {p k : ℕ} [hp : Fact p.Prime]
    (hH : Nat.card H = k * p) : Nat.card (Sylow p H) ∣ k := by
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p H))
  have hndvd : ¬ p ∣ Nat.card (Sylow p H) := not_dvd_card_sylow p H
  have hdvd : Nat.card (Sylow p H) ∣ k * p := by
    rw [← hH]
    exact P.card_dvd_index.trans (Subgroup.index_dvd_card _)
  have hcop : Nat.Coprime (Nat.card (Sylow p H)) p :=
    (hp.out.coprime_iff_not_dvd.mpr hndvd).symm
  exact hcop.dvd_of_dvd_mul_right hdvd

private lemma order48_factorization_mul_self {p k : ℕ}
    (hp : p.Prime) (hpk : ¬ p ∣ k) : (k * p).factorization p = 1 := by
  have hk0 : k ≠ 0 := fun h => hpk (h ▸ dvd_zero p)
  rw [Nat.factorization_mul hk0 hp.ne_zero, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpk, hp.factorization_self, zero_add]

private lemma order48_card_sylow_subgroup_eq_prime
    {H : Type*} [Group H] [Finite H] {p k : ℕ} [hp : Fact p.Prime]
    (hH : Nat.card H = k * p) (hpk : ¬ p ∣ k) (P : Sylow p H) :
    Nat.card (P : Subgroup H) = p := by
  rw [Sylow.card_eq_multiplicity, hH,
    order48_factorization_mul_self hp.out hpk, pow_one]

private lemma order48_exists_char_of_card_sylow_eq_one
    {H : Type*} [Group H] [Finite H] {p k : ℕ} [hp : Fact p.Prime]
    (hH : Nat.card H = k * p) (hpk : ¬ p ∣ k)
    (h1 : Nat.card (Sylow p H) = 1) :
    ∃ R : Subgroup H, R.Characteristic ∧ Nat.card R = p := by
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p H))
  haveI : Subsingleton (Sylow p H) := (Nat.card_eq_one_iff_unique.mp h1).1
  have hnorm : (P : Subgroup H).Normal := Sylow.normal_of_subsingleton P
  have hchar : (P : Subgroup H).Characteristic :=
    Sylow.characteristic_of_normal P hnorm
  exact ⟨P, hchar, order48_card_sylow_subgroup_eq_prime hH hpk P⟩

private lemma order48_card_map_subtype
    {H : Type*} [Group H] {N : Subgroup H} (R : Subgroup N) :
    Nat.card (R.map N.subtype) = Nat.card R :=
  (Nat.card_congr (Subgroup.equivMapOfInjective R N.subtype
    N.subtype_injective).toEquiv).symm

private lemma order48_false_of_normal_has_characteristic_card_three [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4)
    (N : Subgroup G) [N.Normal] (R : Subgroup N) [R.Characteristic]
    (hRcard : Nat.card R = 3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set Q : Subgroup G := R.map N.subtype with hQdef
  haveI hQnorm : Q.Normal := by
    rw [hQdef]
    infer_instance
  have hQcard : Nat.card Q = 3 := by
    rw [hQdef, order48_card_map_subtype, hRcard]
  have hpQ : IsPGroup 3 Q := IsPGroup.iff_card.mpr ⟨1, by simpa using hQcard⟩
  obtain ⟨P, hQP⟩ := hpQ.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup G) = 3 :=
    card_sylow_three_subgroup_of_card_48 hG P
  have hQP_eq : Q = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hQP (by rw [hQcard, hPcard])
  have hPnorm : (P : Subgroup G).Normal := by
    rw [← hQP_eq]
    exact hQnorm
  haveI := Sylow.unique_of_normal P hPnorm
  have : Nat.card (Sylow 3 G) = 1 := Nat.card_unique
  omega

/-- In the four-Sylow-three branch, a normal subgroup cannot have order `6`.
Its unique Sylow `3`-subgroup would be characteristic, hence would give a
normal Sylow `3`-subgroup of the ambient group. -/
theorem order48_no_normal_subgroup_card_six [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4)
    (N : Subgroup G) [N.Normal] : Nat.card N ≠ 6 := by
  intro hNcard
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h63 : Nat.card N = 2 * 3 := by rw [hNcard]
  have hn3 : Nat.card (Sylow 3 N) = 1 := by
    have hdvd := order48_card_sylow_dvd_of_card_eq_mul h63
    have hmod := card_sylow_modEq_one 3 N
    have key : ∀ n ∈ Nat.divisors 2, n % 3 = 1 % 3 → n = 1 := by decide
    exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod
  obtain ⟨R, hRchar, hRcard⟩ :=
    order48_exists_char_of_card_sylow_eq_one h63 (by norm_num) hn3
  haveI := hRchar
  exact order48_false_of_normal_has_characteristic_card_three
    hG hSyl N R hRcard

/-- A normal subgroup of order `12` in the four-Sylow-three branch is `A₄`.
Indeed it cannot have a unique Sylow `3`-subgroup, while the order-`12`
classification leaves only `A₄` when the Sylow count is four. -/
theorem order48_normal_subgroup_card_twelve_equiv_A4 [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4)
    (N : Subgroup G) [N.Normal] (hNcard : Nat.card N = 12) :
    Nonempty (N ≃* fourP_A4) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hN123 : Nat.card N = 4 * 3 := by rw [hNcard]
  have hn3cases : Nat.card (Sylow 3 N) = 1 ∨ Nat.card (Sylow 3 N) = 4 := by
    have hdvd := order48_card_sylow_dvd_of_card_eq_mul hN123
    have hmod := card_sylow_modEq_one 3 N
    have key : ∀ n ∈ Nat.divisors 4, n % 3 = 1 % 3 → n = 1 ∨ n = 4 := by
      decide
    exact key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) hmod
  have hn3 : Nat.card (Sylow 3 N) = 4 := by
    rcases hn3cases with hn1 | hn4
    · obtain ⟨R, hRchar, hRcard⟩ :=
        order48_exists_char_of_card_sylow_eq_one hN123 (by norm_num) hn1
      haveI := hRchar
      exact (order48_false_of_normal_has_characteristic_card_three
        hG hSyl N R hRcard).elim
    · exact hn4
  exact fourP_12_equiv_A4_of_card_sylow_three_eq_four hNcard hn3

/-- With four Sylow `3`-subgroups, each Sylow normalizer has order `12`. -/
theorem order48_card_normalizer_sylow_three_of_card_sylow_three_eq_four
    [Finite G] (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4)
    (P : Sylow 3 G) : Nat.card (Subgroup.normalizer (P : Set G)) = 12 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hidx : (Subgroup.normalizer (P : Set G)).index = 4 := by
    rwa [← Sylow.card_eq_index_normalizer P]
  have hcard := (Subgroup.normalizer (P : Set G)).card_mul_index
  rw [hidx, hG] at hcard
  omega

/-- The conjugation action on the four Sylow `3`-subgroups has kernel order
`2`, `4`, `6`, or `12`.  These are the four structural branches of the
residual classification. -/
theorem order48_sylow_three_conj_action_kernel_cases [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4) :
    ∃ ψ : G →* Equiv.Perm (Fin 4),
      Nat.card ψ.ker = 2 ∨ Nat.card ψ.ker = 4 ∨
        Nat.card ψ.ker = 6 ∨ Nat.card ψ.ker = 12 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  have hfincard : Fintype.card (Sylow 3 G) = 4 := by
    rwa [← Nat.card_eq_fintype_card]
  let ε : Sylow 3 G ≃ Fin 4 := by
    rw [← hfincard]
    exact Fintype.equivFin _
  let φ := MulAction.toPermHom G (Sylow 3 G)
  let ψ : G →* Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom ε).toMonoidHom.comp φ
  obtain ⟨P0⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  have hker_le : ψ.ker ≤ Subgroup.normalizer (P0 : Set G) := by
    intro g hg
    have hgψ := MonoidHom.mem_ker.mp hg
    have hgφ : φ g = 1 := by
      have hgφ' : ε.permCongr (φ g) = 1 := hgψ
      have hgφ'' : ε.permCongr (φ g) = ε.permCongr 1 := by
        have h_one : ε.permCongr 1 = (1 : Equiv.Perm (Fin 4)) := by
          ext x
          simp [Equiv.permCongr_apply]
        rw [h_one]
        exact hgφ'
      exact ε.permCongr.injective hgφ''
    rw [← Sylow.stabilizer_eq_normalizer, MulAction.mem_stabilizer_iff]
    exact Equiv.Perm.ext_iff.mp hgφ P0
  have hnorm : Nat.card (Subgroup.normalizer (P0 : Set G)) = 12 :=
    order48_card_normalizer_sylow_three_of_card_sylow_three_eq_four hG hSyl P0
  have hker_dvd : Nat.card ψ.ker ∣ 12 :=
    hnorm ▸ Subgroup.card_dvd_of_le hker_le
  have hidx : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
  have hmul := ψ.ker.card_mul_index
  rw [hidx, hG] at hmul
  have hrange_dvd : Nat.card ψ.range ∣ 24 := by
    have h := Subgroup.card_subgroup_dvd_card ψ.range
    have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [hperm] at h
    exact h
  have hrange_le : Nat.card ψ.range ≤ 24 :=
    Nat.le_of_dvd (by norm_num) hrange_dvd
  have hker_pos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hker_le_card : Nat.card ψ.ker ≤ 12 :=
    Nat.le_of_dvd (by norm_num) hker_dvd
  refine ⟨ψ, ?_⟩
  interval_cases hk : Nat.card ψ.ker
  · exfalso
    omega
  · exact Or.inl rfl
  · have hrange : Nat.card ψ.range = 16 := by omega
    rw [hrange] at hrange_dvd
    norm_num at hrange_dvd
  · exact Or.inr (Or.inl rfl)
  · norm_num at hker_dvd
  · exact Or.inr (Or.inr (Or.inl rfl))
  · norm_num at hker_dvd
  · norm_num at hker_dvd
  · norm_num at hker_dvd
  · norm_num at hker_dvd
  · norm_num at hker_dvd
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- Refined kernel/image alternatives for the action on the four Sylow
`3`-subgroups.  A kernel of order `6` is impossible; the remaining images are
`S₄`, `A₄`, or a subgroup of order `4`. -/
theorem order48_sylow_three_conj_action_kernel_range_cases [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4) :
    ∃ ψ : G →* Equiv.Perm (Fin 4),
      (Nat.card ψ.ker = 2 ∧ ψ.range = ⊤) ∨
      (Nat.card ψ.ker = 4 ∧ ψ.range = alternatingGroup (Fin 4)) ∨
      (Nat.card ψ.ker = 12 ∧ Nonempty (ψ.ker ≃* fourP_A4) ∧
        Nat.card ψ.range = 4) := by
  obtain ⟨ψ, hker⟩ :=
    order48_sylow_three_conj_action_kernel_cases hG hSyl
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hmul := ψ.ker.card_mul_index
  rw [Subgroup.index_ker ψ, hG] at hmul
  refine ⟨ψ, ?_⟩
  rcases hker with h2 | h4 | h6 | h12
  · rw [h2] at hmul
    have hrange : Nat.card ψ.range = 24 := by omega
    exact Or.inl ⟨h2, Subgroup.eq_top_of_card_eq ψ.range (by
      rw [hrange, hperm])⟩
  · rw [h4] at hmul
    have hrange : Nat.card ψ.range = 12 := by omega
    have hidx : ψ.range.index = 2 := by
      have hcard := ψ.range.card_mul_index
      rw [hrange, hperm] at hcard
      omega
    exact Or.inr (Or.inl ⟨h4,
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx⟩)
  · rw [h6] at hmul
    exact (order48_no_normal_subgroup_card_six hG hSyl ψ.ker) h6 |>.elim
  · rw [h12] at hmul
    exact Or.inr (Or.inr ⟨h12,
      order48_normal_subgroup_card_twelve_equiv_A4 hG hSyl ψ.ker h12, by omega⟩)

/-- A full `S₄` image identifies the quotient by the action kernel with
`S₄`. -/
theorem order48_quotient_ker_mulEquiv_S4_of_range_top
    (ψ : G →* Equiv.Perm (Fin 4)) (hψrange : ψ.range = ⊤) :
    Nonempty (G ⧸ ψ.ker ≃* Equiv.Perm (Fin 4)) := by
  exact ⟨((QuotientGroup.quotientKerEquivRange ψ).trans
    (MulEquiv.subgroupCongr hψrange)).trans Subgroup.topEquiv⟩

/-- An alternating image identifies the quotient by the action kernel with
`A₄`. -/
theorem order48_quotient_ker_mulEquiv_A4_of_range_alt
    (ψ : G →* Equiv.Perm (Fin 4))
    (hψrange : ψ.range = alternatingGroup (Fin 4)) :
    Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4)) := by
  exact ⟨(QuotientGroup.quotientKerEquivRange ψ).trans
    (MulEquiv.subgroupCongr hψrange)⟩

/-- Structural reduction for the residual branch.  The group is an extension
of `S₄` by a kernel of order `2`, an extension of `A₄` by a kernel of order
`4`, or an extension of a group of order `4` by a normal `A₄`. -/
theorem order48_four_sylow_three_extension_cases [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4) :
    ∃ ψ : G →* Equiv.Perm (Fin 4),
      (Nat.card ψ.ker = 2 ∧
        Nonempty (G ⧸ ψ.ker ≃* Equiv.Perm (Fin 4))) ∨
      (Nat.card ψ.ker = 4 ∧
        Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4))) ∨
      (Nat.card ψ.ker = 12 ∧ Nonempty (ψ.ker ≃* fourP_A4) ∧
        Nat.card (G ⧸ ψ.ker) = 4) := by
  obtain ⟨ψ, hψ⟩ := order48_sylow_three_conj_action_kernel_range_cases hG hSyl
  refine ⟨ψ, ?_⟩
  rcases hψ with h2 | h4 | h12
  · exact Or.inl ⟨h2.1,
      order48_quotient_ker_mulEquiv_S4_of_range_top ψ h2.2⟩
  · exact Or.inr (Or.inl ⟨h4.1,
      order48_quotient_ker_mulEquiv_A4_of_range_alt ψ h4.2⟩)
  · exact Or.inr (Or.inr ⟨h12.1, h12.2.1, by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
      exact h12.2.2⟩)

end Smallgroups.UsefulTheorems
