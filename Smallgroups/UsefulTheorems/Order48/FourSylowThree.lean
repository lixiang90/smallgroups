/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.Sylow
import Smallgroups.UsefulTheorems.Order4P_12
import Smallgroups.UsefulTheorems.Order36

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

private theorem order48_card_mulAut_elemAbelianRep_two :
    Nat.card (MulAut (ElemAbelianRep 2)) = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

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
`2`, `4`, or `6`.  Order `12` would make a Sylow normalizer normal and hence
force a normal Sylow `3`-subgroup. -/
theorem order48_sylow_three_conj_action_kernel_cases [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4) :
    ∃ ψ : G →* Equiv.Perm (Fin 4),
      Nat.card ψ.ker = 2 ∨ Nat.card ψ.ker = 4 ∨
        Nat.card ψ.ker = 6 := by
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
  · exact Or.inr (Or.inr rfl)
  · norm_num at hker_dvd
  · norm_num at hker_dvd
  · norm_num at hker_dvd
  · norm_num at hker_dvd
  · norm_num at hker_dvd
  · have hker_eq : ψ.ker = Subgroup.normalizer (P0 : Set G) :=
      Subgroup.eq_of_le_of_card_ge hker_le (by rw [hnorm, hk])
    have hnorm_normal : (Subgroup.normalizer (P0 : Set G)).Normal :=
      hker_eq ▸ MonoidHom.normal_ker ψ
    have hPnormal : (P0 : Subgroup G).Normal :=
      Sylow.normal_of_normalizer_normal P0 hnorm_normal
    haveI := Sylow.unique_of_normal P0 hPnormal
    have : Nat.card (Sylow 3 G) = 1 := Nat.card_unique
    omega

/-- Refined kernel/image alternatives for the action on the four Sylow
`3`-subgroups.  A kernel of order `6` is impossible, so the image is `S₄` or
`A₄`. -/
theorem order48_sylow_three_conj_action_kernel_range_cases [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4) :
    ∃ ψ : G →* Equiv.Perm (Fin 4),
      (Nat.card ψ.ker = 2 ∧ ψ.range = ⊤) ∨
      (Nat.card ψ.ker = 4 ∧ ψ.range = alternatingGroup (Fin 4)) := by
  obtain ⟨ψ, hker⟩ :=
    order48_sylow_three_conj_action_kernel_cases hG hSyl
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hmul := ψ.ker.card_mul_index
  rw [Subgroup.index_ker ψ, hG] at hmul
  refine ⟨ψ, ?_⟩
  rcases hker with h2 | h4 | h6
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
    exact Or.inr ⟨h4, Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx⟩
  · rw [h6] at hmul
    exact (order48_no_normal_subgroup_card_six hG hSyl ψ.ker) h6 |>.elim

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

/-- Structural reduction for the residual branch.  The group is either an
extension of `S₄` by a kernel of order `2`, or an extension of `A₄` by a
kernel of order `4`. -/
theorem order48_four_sylow_three_extension_cases [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4) :
    ∃ ψ : G →* Equiv.Perm (Fin 4),
      (Nat.card ψ.ker = 2 ∧
        Nonempty (G ⧸ ψ.ker ≃* Equiv.Perm (Fin 4))) ∨
      (Nat.card ψ.ker = 4 ∧
        Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4))) := by
  obtain ⟨ψ, hψ⟩ := order48_sylow_three_conj_action_kernel_range_cases hG hSyl
  refine ⟨ψ, ?_⟩
  rcases hψ with h2 | h4
  · exact Or.inl ⟨h2.1,
      order48_quotient_ker_mulEquiv_S4_of_range_top ψ h2.2⟩
  · exact Or.inr ⟨h4.1,
      order48_quotient_ker_mulEquiv_A4_of_range_alt ψ h4.2⟩

/-- Every normal subgroup of order `2` is central.  Conjugation acts through
the trivial automorphism group of `C₂`. -/
theorem normal_subgroup_card_two_le_center [Finite G]
    (N : Subgroup G) [N.Normal] (hNcard : Nat.card N = 2) :
    N ≤ Subgroup.center G := by
  haveI hNcyc : IsCyclic N := isCyclic_of_prime_card hNcard
  have hAutCard : Nat.card (MulAut N) = 1 := by
    rw [IsCyclic.card_mulAut, hNcard]
    decide
  haveI : Subsingleton (MulAut N) :=
    (Nat.card_eq_one_iff_unique.mp hAutCard).1
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  have hfix : MulAut.conjNormal (H := N) g ⟨n, hn⟩ = ⟨n, hn⟩ := by
    rw [Subsingleton.elim (MulAut.conjNormal (H := N) g) 1]
    rfl
  have hconj : g * n * g⁻¹ = n := by
    simpa only [MulAut.conjNormal_apply] using congrArg Subtype.val hfix
  calc
    g * n = (g * n * g⁻¹) * g := by simp [mul_assoc]
    _ = n * g := by rw [hconj]

/-- `A₄` has no normal subgroup of order `2`. -/
theorem order48_A4_no_normal_subgroup_card_two
    (N : Subgroup (alternatingGroup (Fin 4))) [N.Normal] :
    Nat.card N ≠ 2 := by
  intro hNcard
  have hcenter := normal_subgroup_card_two_le_center N hNcard
  rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 4))] at hcenter
  have hNbot : N = ⊥ := le_bot_iff.mp hcenter
  rw [hNbot, Subgroup.card_bot] at hNcard
  omega

/-- `A₄` has no normal subgroup of order `3`. -/
theorem order48_A4_no_normal_subgroup_card_three
    (N : Subgroup (alternatingGroup (Fin 4))) [N.Normal] :
    Nat.card N ≠ 3 := by
  intro hNcard
  have hquot : Nat.card (alternatingGroup (Fin 4) ⧸ N) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hNcard, card_fourP_A4] at h
    omega
  have hquot_sq : Nat.card (alternatingGroup (Fin 4) ⧸ N) = 2 ^ 2 := by
    omega
  haveI : IsMulCommutative (alternatingGroup (Fin 4) ⧸ N) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hquot_sq
  have hcomm : commutator (alternatingGroup (Fin 4)) ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hklein : alternatingGroup.kleinFour (Fin 4) ≤ N := by
    simpa [alternatingGroup.kleinFour_eq_commutator (by simp : Nat.card (Fin 4) = 4)]
      using hcomm
  have hdvd := Subgroup.card_dvd_of_le hklein
  rw [alternatingGroup.kleinFour_card_of_card_eq_four (by simp), hNcard] at hdvd
  norm_num at hdvd

/-- `A₄` has no normal subgroup of order `6`. -/
theorem order48_A4_no_normal_subgroup_card_six
    (N : Subgroup (alternatingGroup (Fin 4))) [N.Normal] :
    Nat.card N ≠ 6 := by
  intro hNcard
  have hquot : Nat.card (alternatingGroup (Fin 4) ⧸ N) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hNcard, card_fourP_A4] at h
    omega
  haveI : IsCyclic (alternatingGroup (Fin 4) ⧸ N) :=
    isCyclic_of_prime_card hquot
  letI : CommGroup (alternatingGroup (Fin 4) ⧸ N) := IsCyclic.commGroup
  have hcomm : commutator (alternatingGroup (Fin 4)) ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hklein : alternatingGroup.kleinFour (Fin 4) ≤ N := by
    simpa [alternatingGroup.kleinFour_eq_commutator (by simp : Nat.card (Fin 4) = 4)]
      using hcomm
  have hdvd := Subgroup.card_dvd_of_le hklein
  rw [alternatingGroup.kleinFour_card_of_card_eq_four (by simp), hNcard] at hdvd
  norm_num at hdvd

/-- A homomorphism from `A₄` to a group of order `6` has image of order `1`
or `3`.  This is the action dichotomy needed for an elementary-abelian
order-`4` kernel, whose automorphism group has order `6`. -/
theorem order48_A4_hom_range_card_one_or_three
    {H : Type*} [Group H] [Finite H] (hHcard : Nat.card H = 6)
    (f : alternatingGroup (Fin 4) →* H) :
    Nat.card f.range = 1 ∨ Nat.card f.range = 3 := by
  have hrange_dvd : Nat.card f.range ∣ 6 := by
    simpa [hHcard] using Subgroup.card_subgroup_dvd_card f.range
  have hrange_le : Nat.card f.range ≤ 6 :=
    Nat.le_of_dvd (by norm_num) hrange_dvd
  have hrange_pos : 0 < Nat.card f.range := Nat.card_pos
  have hmul := f.ker.card_mul_index
  rw [Subgroup.index_ker f, card_fourP_A4] at hmul
  interval_cases hrange : Nat.card f.range
  · exact Or.inl rfl
  · have hker6 : Nat.card f.ker = 6 := by omega
    exact (order48_A4_no_normal_subgroup_card_six f.ker) hker6 |>.elim
  · exact Or.inr rfl
  · have hker3 : Nat.card f.ker = 3 := by omega
    exact (order48_A4_no_normal_subgroup_card_three f.ker) hker3 |>.elim
  · norm_num at hrange_dvd
  · have hker2 : Nat.card f.ker = 2 := by omega
    exact (order48_A4_no_normal_subgroup_card_two f.ker) hker2 |>.elim

/-- A cyclic normal subgroup of order `4` with quotient `A₄` is central.
The conjugation action factors through `A₄`, while every homomorphism from
`A₄` to the order-`2` automorphism group of `C₄` is trivial. -/
theorem normal_cyclic_subgroup_card_four_A4_quotient_le_center [Finite G]
    (K : Subgroup G) [K.Normal] [IsCyclic K]
    (hKcard : Nat.card K = 4)
    (hquot : Nonempty (G ⧸ K ≃* alternatingGroup (Fin 4))) :
    K ≤ Subgroup.center G := by
  have hKcomm : ∀ x y : K, x * y = y * x :=
    fun x y => IsCyclic.commGroup.mul_comm x y
  have hAutK : Nat.card (MulAut K) = 2 := by
    rw [IsCyclic.card_mulAut K, hKcard]
    decide
  let φ : G →* MulAut K := MulAut.conjNormal
  have hKker : K ≤ φ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change k * (x : G) * k⁻¹ = (x : G)
    have hcomm : (⟨k, hk⟩ : K) * x = x * ⟨k, hk⟩ := hKcomm _ _
    have hcommG : k * (x : G) = (x : G) * k := congrArg Subtype.val hcomm
    calc
      k * (x : G) * k⁻¹ = ((x : G) * k) * k⁻¹ := by rw [hcommG]
      _ = (x : G) := by group
  let φQ : G ⧸ K →* MulAut K := QuotientGroup.lift K φ hKker
  obtain ⟨e⟩ := hquot
  let ρ : alternatingGroup (Fin 4) →* MulAut K :=
    φQ.comp e.symm.toMonoidHom
  have hρ : ρ = 1 := order36_A4_hom_to_order_two_trivial hAutK ρ
  have hφ : φ = 1 := by
    apply MonoidHom.ext
    intro g
    have hq : ρ (e ((QuotientGroup.mk' K) g)) = 1 := by
      rw [hρ]
      rfl
    simpa [ρ, φQ] using hq
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  let kk : K := ⟨k, hk⟩
  have hg : φ g = 1 := congrArg (fun f : G →* MulAut K => f g) hφ
  have happ : (φ g) kk = kk := by
    rw [hg]
    rfl
  have hconj : g * k * g⁻¹ = k := by
    have happ_coe := congrArg (fun x : K => (x : G)) happ
    simpa [φ, kk] using happ_coe
  calc
    g * k = (g * k * g⁻¹) * g := by group
    _ = k * g := by rw [hconj]

/-- For an elementary-abelian normal subgroup `K` of order `4` with quotient
`A₄`, the quotient conjugation action is either trivial (so `K` is central)
or has image of order `3`. -/
theorem normal_elemAbelian_card_four_A4_quotient_action_cases [Finite G]
    (K : Subgroup G) [K.Normal] (hKcard : Nat.card K = 4)
    (hKtype : Nonempty (K ≃* ElemAbelianRep 2))
    (hquot : Nonempty (G ⧸ K ≃* alternatingGroup (Fin 4))) :
    K ≤ Subgroup.center G ∨
      ∃ φQ : G ⧸ K →* MulAut K,
        (∀ g : G, φQ ((QuotientGroup.mk' K) g) = MulAut.conjNormal g) ∧
        Nat.card φQ.range = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hKsq : Nat.card K = 2 ^ 2 := by omega
  letI : CommGroup K := IsPGroup.commGroupOfCardEqPrimeSq hKsq
  obtain ⟨eK⟩ := hKtype
  have hAutK : Nat.card (MulAut K) = 6 := by
    rw [Nat.card_congr (MulAut.congr eK).toEquiv,
      order48_card_mulAut_elemAbelianRep_two]
  let φ : G →* MulAut K := MulAut.conjNormal
  have hKker : K ≤ φ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change k * (x : G) * k⁻¹ = (x : G)
    have hcomm : (⟨k, hk⟩ : K) * x = x * ⟨k, hk⟩ := mul_comm _ _
    have hcommG : k * (x : G) = (x : G) * k := congrArg Subtype.val hcomm
    calc
      k * (x : G) * k⁻¹ = ((x : G) * k) * k⁻¹ := by rw [hcommG]
      _ = (x : G) := by group
  let φQ : G ⧸ K →* MulAut K := QuotientGroup.lift K φ hKker
  obtain ⟨e⟩ := hquot
  let ρ : alternatingGroup (Fin 4) →* MulAut K :=
    φQ.comp e.symm.toMonoidHom
  have hrange_eq : ρ.range = φQ.range := by
    change (φQ.comp e.symm.toMonoidHom).range = φQ.range
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr e.symm.surjective]
    exact (MonoidHom.range_eq_map φQ).symm
  rcases order48_A4_hom_range_card_one_or_three hAutK ρ with hρ1 | hρ3
  · left
    have hρbot : ρ.range = ⊥ := ρ.range.eq_bot_of_card_eq hρ1
    have hρ : ρ = 1 := MonoidHom.range_eq_bot_iff.mp hρbot
    have hφ : φ = 1 := by
      apply MonoidHom.ext
      intro g
      have hq : ρ (e ((QuotientGroup.mk' K) g)) = 1 := by
        rw [hρ]
        rfl
      simpa [ρ, φQ] using hq
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    let kk : K := ⟨k, hk⟩
    have hg : φ g = 1 := congrArg (fun f : G →* MulAut K => f g) hφ
    have happ : (φ g) kk = kk := by
      rw [hg]
      rfl
    have hconj : g * k * g⁻¹ = k := by
      have happ_coe := congrArg (fun x : K => (x : G)) happ
      simpa [φ, kk] using happ_coe
    calc
      g * k = (g * k * g⁻¹) * g := by group
      _ = k * g := by rw [hconj]
  · right
    refine ⟨φQ, ?_, ?_⟩
    · intro g
      rfl
    · rw [← hrange_eq]
      exact hρ3

/-- The residual extension cases with every kernel and quotient of order at
most four replaced by its prime or prime-square isomorphism type. -/
theorem order48_four_sylow_three_typed_extension_cases [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4) :
    ∃ ψ : G →* Equiv.Perm (Fin 4),
      (Nonempty (ψ.ker ≃* CyclicRep 2) ∧ ψ.ker ≤ Subgroup.center G ∧
        Nonempty (G ⧸ ψ.ker ≃* Equiv.Perm (Fin 4))) ∨
      (((Nonempty (ψ.ker ≃* CyclicRep (2 ^ 2)) ∧
          ψ.ker ≤ Subgroup.center G) ∨
          (Nonempty (ψ.ker ≃* ElemAbelianRep 2) ∧
            (ψ.ker ≤ Subgroup.center G ∨
              ∃ φQ : G ⧸ ψ.ker →* MulAut ψ.ker,
                (∀ g : G,
                  φQ ((QuotientGroup.mk' ψ.ker) g) = MulAut.conjNormal g) ∧
                Nat.card φQ.range = 3))) ∧
        Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4))) := by
  obtain ⟨ψ, hψ⟩ := order48_four_sylow_three_extension_cases hG hSyl
  refine ⟨ψ, ?_⟩
  rcases hψ with h2 | h4
  · exact Or.inl ⟨prime_classification (by norm_num) h2.1,
      normal_subgroup_card_two_le_center ψ.ker h2.1, h2.2⟩
  · have hker4 : Nat.card ψ.ker = 2 ^ 2 := by omega
    rcases prime_sq_classification hker4 with hcyc | helem
    · obtain ⟨e⟩ := hcyc
      haveI : IsCyclic ψ.ker := e.isCyclic.mpr inferInstance
      exact Or.inr ⟨Or.inl ⟨⟨e⟩,
        normal_cyclic_subgroup_card_four_A4_quotient_le_center
          ψ.ker h4.1 h4.2⟩, h4.2⟩
    · exact Or.inr ⟨Or.inr ⟨helem,
        normal_elemAbelian_card_four_A4_quotient_action_cases
          ψ.ker h4.1 helem h4.2⟩, h4.2⟩

end Smallgroups.UsefulTheorems
