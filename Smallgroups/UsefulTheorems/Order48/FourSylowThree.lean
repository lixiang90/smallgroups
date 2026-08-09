/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.Sylow
import Smallgroups.UsefulTheorems.Order4P_12
import Smallgroups.UsefulTheorems.Order24
import Smallgroups.UsefulTheorems.Order36
import Smallgroups.UsefulTheorems.PGroupGeneration.CentralExtension

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
      (∀ P : Sylow 3 G, ψ.ker ≤ Subgroup.normalizer (P : Set G)) ∧
        (Nat.card ψ.ker = 2 ∨ Nat.card ψ.ker = 4 ∨
          Nat.card ψ.ker = 6) := by
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
  have hker_le_all : ∀ P : Sylow 3 G,
      ψ.ker ≤ Subgroup.normalizer (P : Set G) := by
    intro P g hg
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
    exact Equiv.Perm.ext_iff.mp hgφ P
  have hker_le : ψ.ker ≤ Subgroup.normalizer (P0 : Set G) := hker_le_all P0
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
  refine ⟨ψ, hker_le_all, ?_⟩
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
      (∀ P : Sylow 3 G, ψ.ker ≤ Subgroup.normalizer (P : Set G)) ∧
        ((Nat.card ψ.ker = 2 ∧ ψ.range = ⊤) ∨
        (Nat.card ψ.ker = 4 ∧ ψ.range = alternatingGroup (Fin 4))) := by
  obtain ⟨ψ, hnormalizes, hker⟩ :=
    order48_sylow_three_conj_action_kernel_cases hG hSyl
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hmul := ψ.ker.card_mul_index
  rw [Subgroup.index_ker ψ, hG] at hmul
  refine ⟨ψ, hnormalizes, ?_⟩
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
      (∀ P : Sylow 3 G, ψ.ker ≤ Subgroup.normalizer (P : Set G)) ∧
        ((Nat.card ψ.ker = 2 ∧
          Nonempty (G ⧸ ψ.ker ≃* Equiv.Perm (Fin 4))) ∨
        (Nat.card ψ.ker = 4 ∧
          Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4)))) := by
  obtain ⟨ψ, hnormalizes, hψ⟩ :=
    order48_sylow_three_conj_action_kernel_range_cases hG hSyl
  refine ⟨ψ, hnormalizes, ?_⟩
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

/-- If a normal subgroup of order four with `A₄` quotient normalizes every
Sylow `3`-subgroup, then it is central.  This is the extra information carried
by the kernel of the conjugation action on the four Sylow subgroups. -/
theorem normal_subgroup_card_four_A4_quotient_le_center_of_normalizes_sylow
    [Finite G] (hG : Nat.card G = 48) (K : Subgroup G) [K.Normal]
    (hKcard : Nat.card K = 4)
    (hquot : Nonempty (G ⧸ K ≃* alternatingGroup (Fin 4)))
    (hnormalizes : ∀ P : Sylow 3 G, K ≤ Subgroup.normalizer (P : Set G)) :
    K ≤ Subgroup.center G := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hKsq : Nat.card K = 2 ^ 2 := by omega
  letI : CommGroup K := IsPGroup.commGroupOfCardEqPrimeSq hKsq
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 G))
  have hPcard : Nat.card (P : Subgroup G) = 3 :=
    card_sylow_three_subgroup_of_card_48 hG P
  have hdisj : Disjoint K (P : Subgroup G) :=
    Subgroup.disjoint_of_coprime_natCard (by
      rw [hKcard, hPcard]
      norm_num)
  have hcomm_le_P : ⁅K, (P : Subgroup G)⁆ ≤ (P : Subgroup G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp (hnormalizes P)
  have hcomm_le_K : ⁅K, (P : Subgroup G)⁆ ≤ K :=
    Subgroup.commutator_le_left K (P : Subgroup G)
  have hcomm_bot : ⁅K, (P : Subgroup G)⁆ = ⊥ := by
    rw [← le_bot_iff]
    exact (le_inf hcomm_le_K hcomm_le_P).trans hdisj.eq_bot.le
  have hKcentP : K ≤ Subgroup.centralizer (P : Subgroup G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot
  have hPcentK : (P : Subgroup G) ≤ Subgroup.centralizer K :=
    Subgroup.le_centralizer_iff.mp hKcentP
  let S : Subgroup G := Subgroup.normalClosure (P : Set G)
  have hScentK : S ≤ Subgroup.centralizer K := by
    dsimp [S]
    apply Subgroup.normalClosure_le_normal
    exact hPcentK
  obtain ⟨e⟩ := hquot
  let q : G →* alternatingGroup (Fin 4) :=
    e.toMonoidHom.comp (QuotientGroup.mk' K)
  have hqsurj : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective K)
  have hqker : q.ker = K := by
    ext g
    simp [q]
  let J : Subgroup (alternatingGroup (Fin 4)) := S.map q
  haveI hJnormal : J.Normal :=
    Subgroup.Normal.map (inferInstance : S.Normal) q hqsurj
  have hqPinj : Function.Injective (q.comp (P : Subgroup G).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxK : (x : G) ∈ K := by
      rw [← hqker, MonoidHom.mem_ker]
      exact hx
    have hxinf : (x : G) ∈ K ⊓ (P : Subgroup G) := ⟨hxK, x.property⟩
    have hxone : (x : G) = 1 := by
      rw [hdisj.eq_bot] at hxinf
      exact Subgroup.mem_bot.mp hxinf
    exact Subtype.ext hxone
  have hPmapcard : Nat.card ((P : Subgroup G).map q) = 3 := by
    have hrange : (q.comp (P : Subgroup G).subtype).range =
        (P : Subgroup G).map q := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hqPinj).toEquiv).symm.trans hPcard
  have hPmap_le_J : (P : Subgroup G).map q ≤ J := by
    dsimp [J, S]
    exact Subgroup.map_mono Subgroup.subset_normalClosure
  have hthree_dvd : 3 ∣ Nat.card J := by
    rw [← hPmapcard]
    exact Subgroup.card_dvd_of_le hPmap_le_J
  have hJdvd : Nat.card J ∣ 12 := by
    have h := J.card_subgroup_dvd_card
    rw [card_order36_A4] at h
    exact h
  have hJle : Nat.card J ≤ 12 := Nat.le_of_dvd (by norm_num) hJdvd
  have hJcard : Nat.card J = 12 := by
    interval_cases hcard : Nat.card J
    all_goals try { exfalso; norm_num [hcard] at hJdvd }
    all_goals try { exfalso; norm_num [hcard] at hthree_dvd }
    · exact (order48_A4_no_normal_subgroup_card_three J hcard).elim
    · exact (order48_A4_no_normal_subgroup_card_six J hcard).elim
    · rfl
  have hJtop : J = ⊤ :=
    Subgroup.eq_top_of_card_eq J (by rw [hJcard, card_order36_A4])
  have hSKtop : S ⊔ K = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro g
    have hqg : q g ∈ J := by rw [hJtop]; exact Subgroup.mem_top _
    rcases hqg with ⟨s, hsS, hsg⟩
    have hks : g * s⁻¹ ∈ K := by
      rw [← hqker, MonoidHom.mem_ker]
      rw [map_mul, map_inv, hsg]
      group
    have hprod : (g * s⁻¹) * s = g := by group
    rw [← hprod]
    exact (S ⊔ K).mul_mem
      ((show K ≤ S ⊔ K from le_sup_right) hks)
      ((show S ≤ S ⊔ K from le_sup_left) hsS)
  have hKcentK : K ≤ Subgroup.centralizer K :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have htopcentK : (⊤ : Subgroup G) ≤ Subgroup.centralizer K := by
    rw [← hSKtop]
    exact sup_le hScentK hKcentK
  have hKcentTop : K ≤ Subgroup.centralizer (⊤ : Subgroup G) :=
    Subgroup.le_centralizer_iff.mp htopcentK
  simpa [Subgroup.centralizer_univ] using hKcentTop

/-- The residual extension cases with every kernel and quotient of order at
most four replaced by its prime or prime-square isomorphism type. -/
theorem order48_four_sylow_three_typed_extension_cases [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4) :
    ∃ ψ : G →* Equiv.Perm (Fin 4),
      (Nonempty (ψ.ker ≃* CyclicRep 2) ∧ ψ.ker ≤ Subgroup.center G ∧
        Nonempty (G ⧸ ψ.ker ≃* Equiv.Perm (Fin 4))) ∨
      (((Nonempty (ψ.ker ≃* CyclicRep (2 ^ 2)) ∨
          Nonempty (ψ.ker ≃* ElemAbelianRep 2)) ∧
        ψ.ker ≤ Subgroup.center G) ∧
        Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4))) := by
  obtain ⟨ψ, hnormalizes, hψ⟩ :=
    order48_four_sylow_three_extension_cases hG hSyl
  refine ⟨ψ, ?_⟩
  rcases hψ with h2 | h4
  · exact Or.inl ⟨prime_classification (by norm_num) h2.1,
      normal_subgroup_card_two_le_center ψ.ker h2.1, h2.2⟩
  · have hker4 : Nat.card ψ.ker = 2 ^ 2 := by omega
    have hcenter : ψ.ker ≤ Subgroup.center G :=
      normal_subgroup_card_four_A4_quotient_le_center_of_normalizes_sylow
        hG ψ.ker h4.1 h4.2 hnormalizes
    rcases prime_sq_classification hker4 with hcyc | helem
    · exact Or.inr ⟨⟨Or.inl hcyc, hcenter⟩, h4.2⟩
    · exact Or.inr ⟨⟨Or.inr helem, hcenter⟩, h4.2⟩

/-! ### Reduction through a central involution -/

/-- Quotienting a group of order `48` by an involution gives a group of
order `24`. -/
theorem order48_card_quotient_zpowers_of_order_two [Finite G]
    (hG : Nat.card G = 48) {z : G} (hz2 : orderOf z = 2)
    [(Subgroup.zpowers z).Normal] :
    Nat.card (G ⧸ Subgroup.zpowers z) = 24 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.zpowers z)
  rw [Nat.card_zpowers, hz2, hG] at h
  omega

private theorem order48_card_sylow_three_eq_one_of_normal_card_three
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 24)
    (N : Subgroup H) [N.Normal] (hN : Nat.card N = 3) :
    Nat.card (Sylow 3 H) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfact : (Nat.card H).factorization 3 = 1 := by
    rw [hH]
    decide +kernel
  let P : Sylow 3 H := Sylow.ofCard N (by rw [hfact, pow_one, hN])
  have hPnormal : (P : Subgroup H).Normal := by
    dsimp [P]
    infer_instance
  haveI := Sylow.unique_of_normal P hPnormal
  exact Nat.card_unique

private theorem order48_card_sylow_three_prod_of_cards_three_eight
    {N H : Type*} [Group N] [Group H] [Finite N] [Finite H]
    (hN : Nat.card N = 3) (hH : Nat.card H = 8) :
    Nat.card (Sylow 3 (N × H)) = 1 := by
  let K : Subgroup (N × H) := (MonoidHom.snd N H).ker
  haveI : K.Normal := by
    dsimp [K]
    infer_instance
  have hK : Nat.card K = 3 := by
    rw [show K = (⊤ : Subgroup N).prod (⊥ : Subgroup H) by
      dsimp [K]
      rw [MonoidHom.ker_snd]]
    rw [Nat.card_congr (Subgroup.prodEquiv (⊤ : Subgroup N) (⊥ : Subgroup H)).toEquiv,
      Nat.card_prod, Subgroup.card_top, Subgroup.card_bot, hN]
  apply order48_card_sylow_three_eq_one_of_normal_card_three (N := K)
  · rw [Nat.card_prod, hN, hH]
  · exact hK

private theorem order48_card_sylow_three_semidirect_of_cards_three_eight
    {N H : Type*} [Group N] [Group H] [Finite N] [Finite H]
    (φ : H →* MulAut N) (hN : Nat.card N = 3) (hH : Nat.card H = 8) :
    Nat.card (Sylow 3 (SemidirectProduct N H φ)) = 1 := by
  haveI : Finite (SemidirectProduct N H φ) :=
    Finite.of_equiv _ SemidirectProduct.equivProd.symm
  let K : Subgroup (SemidirectProduct N H φ) :=
    (SemidirectProduct.rightHom : SemidirectProduct N H φ →* H).ker
  haveI : K.Normal := by
    dsimp [K]
    infer_instance
  have hK : Nat.card K = 3 := by
    have e : N ≃* (SemidirectProduct.inl :
        N →* SemidirectProduct N H φ).range :=
      MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := φ))
    rw [show K = (SemidirectProduct.inl :
        N →* SemidirectProduct N H φ).range by
      dsimp [K]
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom (φ := φ)]]
    rw [← hN, Nat.card_congr e.toEquiv]
  apply order48_card_sylow_three_eq_one_of_normal_card_three (N := K)
  · rw [SemidirectProduct.card, hN, hH]
  · exact hK

private theorem order48_card_sylow_three_order24_normalC3_reps (i : Fin 12) :
    Nat.card (Sylow 3 (order24_normalC3_reps i)) = 1 := by
  fin_cases i
  · exact order48_card_sylow_three_prod_of_cards_three_eight
      card_order24_C3 card_order24_C8
  · exact order48_card_sylow_three_prod_of_cards_three_eight
      card_order24_C3 card_order24_C4C2
  · exact order48_card_sylow_three_prod_of_cards_three_eight
      card_order24_C3 card_order24_C2C2C2
  · exact order48_card_sylow_three_prod_of_cards_three_eight
      card_order24_C3 card_order24_D8
  · exact order48_card_sylow_three_prod_of_cards_three_eight
      card_order24_C3 card_order24_Q8
  · exact order48_card_sylow_three_semidirect_of_cards_three_eight
      (order24_action order88_chiC8) card_order24_C3 card_order24_C8
  · exact order48_card_sylow_three_semidirect_of_cards_three_eight
      (order24_action order88_chiC4C2_fst) card_order24_C3 card_order24_C4C2
  · exact order48_card_sylow_three_semidirect_of_cards_three_eight
      (order24_action order88_chiC4C2_snd) card_order24_C3 card_order24_C4C2
  · exact order48_card_sylow_three_semidirect_of_cards_three_eight
      (order24_action order88_chiC2C2C2) card_order24_C3 card_order24_C2C2C2
  · exact order48_card_sylow_three_semidirect_of_cards_three_eight
      (order24_action order88_chiD8_rot) card_order24_C3 card_order24_D8
  · exact order48_card_sylow_three_semidirect_of_cards_three_eight
      (order24_action order88_chiD8_ref) card_order24_C3 card_order24_D8
  · exact order48_card_sylow_three_semidirect_of_cards_three_eight
      (order24_action order88_chiQ8) card_order24_C3 card_order24_Q8

private noncomputable def order48_sylow_equiv_of_mulEquiv
    {H : Type*} [Group H] {p : ℕ} (e : G ≃* H) :
    Sylow p G ≃ Sylow p H where
  toFun P := P.comapOfInjective e.symm.toMonoidHom e.symm.injective
    (by rw [MonoidHom.range_eq_top.mpr e.symm.surjective]; exact le_top)
  invFun Q := Q.comapOfInjective e.toMonoidHom e.injective
    (by rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
  left_inv P := by
    apply Sylow.ext
    rw [Sylow.coe_comapOfInjective, Sylow.coe_comapOfInjective, Subgroup.comap_comap]
    have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [h, Subgroup.comap_id]
  right_inv Q := by
    apply Sylow.ext
    rw [Sylow.coe_comapOfInjective, Sylow.coe_comapOfInjective, Subgroup.comap_comap]
    have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
      ext x
      simp
    rw [h, Subgroup.comap_id]

private theorem order48_card_sylow_of_mulEquiv
    {H : Type*} [Group H] (p : ℕ) (e : G ≃* H) :
    Nat.card (Sylow p G) = Nat.card (Sylow p H) :=
  Nat.card_congr (order48_sylow_equiv_of_mulEquiv e)

/-- The four-Sylow-three part of the order-`24` classification consists of
exactly the two representatives with a normal Sylow `2`-subgroup and `S₄`.
This is the form needed after quotienting an order-`48` group by a central
involution. -/
theorem order24_classification_of_card_sylow_three_eq_four
    {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 24) (hSyl : Nat.card (Sylow 3 H) = 4) :
    Nonempty (H ≃* order24_RM) ∨ Nonempty (H ≃* order24_RN) ∨
      Nonempty (H ≃* order24_RO) := by
  obtain ⟨i, hi⟩ := order24_classification hH
  fin_cases i
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (0 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (1 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (2 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (3 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (4 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (5 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (6 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (7 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (8 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (9 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (10 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact (by
      have hc := order48_card_sylow_of_mulEquiv 3 hi.some
      have hrep := order48_card_sylow_three_order24_normalC3_reps (11 : Fin 12)
      simp only [order24_reps, order24_normalC3_reps] at hc hrep
      omega)
  · exact Or.inl (by simpa [order24_reps] using hi)
  · exact Or.inr (Or.inl (by simpa [order24_reps] using hi))
  · exact Or.inr (Or.inr (by simpa [order24_reps] using hi))

/-- If a central subgroup has order `2` or `4`, it contains a central
involution.  In the four-Sylow-three branch, quotienting by that involution
still leaves four Sylow `3`-subgroups: a unique Sylow `3`-subgroup downstairs
would pull back to a forbidden normal subgroup of order `6` upstairs. -/
theorem order48_central_kernel_reduction_to_order24 [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4)
    (K : Subgroup G) (hKcenter : K ≤ Subgroup.center G)
    (hKcard : Nat.card K = 2 ∨ Nat.card K = 4) :
    ∃ z : G, z ∈ K ∧ orderOf z = 2 ∧
      ∃ hzcenter : z ∈ Subgroup.center G,
        letI := normal_of_le_center (Subgroup.zpowers_le.mpr hzcenter)
        Nat.card (G ⧸ Subgroup.zpowers z) = 24 ∧
        Nat.card (Sylow 3 (G ⧸ Subgroup.zpowers z)) = 4 ∧
        (Nonempty ((G ⧸ Subgroup.zpowers z) ≃* order24_RM) ∨
          Nonempty ((G ⧸ Subgroup.zpowers z) ≃* order24_RN) ∨
          Nonempty ((G ⧸ Subgroup.zpowers z) ≃* order24_RO)) := by
  have htwo_dvd : 2 ∣ Nat.card K := by
    rcases hKcard with h2 | h4
    · simp [h2]
    · simp [h4]
  obtain ⟨zK, hzK2⟩ :=
    exists_prime_orderOf_dvd_card' (G := K) 2 htwo_dvd
  let z : G := zK
  have hzK : z ∈ K := zK.property
  have hz2 : orderOf z = 2 :=
    (orderOf_injective K.subtype K.subtype_injective zK).trans hzK2
  have hzcenter : z ∈ Subgroup.center G := hKcenter hzK
  have hZnormal : (Subgroup.zpowers z).Normal :=
    normal_of_le_center (Subgroup.zpowers_le.mpr hzcenter)
  letI : (Subgroup.zpowers z).Normal := hZnormal
  have hQcard : Nat.card (G ⧸ Subgroup.zpowers z) = 24 :=
    order48_card_quotient_zpowers_of_order_two hG hz2
  have hQsyl : Nat.card (Sylow 3 (G ⧸ Subgroup.zpowers z)) = 4 := by
    rcases card_sylow_3_of_card_24_eq_one_or_four hQcard with hQone | hQfour
    · obtain ⟨P⟩ :=
        (Sylow.nonempty : Nonempty (Sylow 3 (G ⧸ Subgroup.zpowers z)))
      haveI : Subsingleton (Sylow 3 (G ⧸ Subgroup.zpowers z)) :=
        (Nat.card_eq_one_iff_unique.mp hQone).1
      have hPnormal : (P : Subgroup (G ⧸ Subgroup.zpowers z)).Normal :=
        Sylow.normal_of_subsingleton P
      let A : Subgroup G :=
        (P : Subgroup (G ⧸ Subgroup.zpowers z)).comap
          (QuotientGroup.mk' (Subgroup.zpowers z))
      have hAnormal : A.Normal := by
        dsimp [A]
        exact hPnormal.comap (QuotientGroup.mk' (Subgroup.zpowers z))
      letI : A.Normal := hAnormal
      have hPcard : Nat.card (P : Subgroup (G ⧸ Subgroup.zpowers z)) = 3 :=
        card_sylow_3_subgroup_of_card_24 hQcard P
      have hZcard : Nat.card (Subgroup.zpowers z) = 2 := by
        rw [Nat.card_zpowers, hz2]
      have hAcard : Nat.card A = 6 := by
        have hpre := QuotientGroup.card_preimage_mk (Subgroup.zpowers z)
          ((P : Subgroup (G ⧸ Subgroup.zpowers z)) :
            Set (G ⧸ Subgroup.zpowers z))
        change Nat.card A = Nat.card (Subgroup.zpowers z) *
          Nat.card (P : Subgroup (G ⧸ Subgroup.zpowers z)) at hpre
        rw [hZcard, hPcard] at hpre
        exact hpre
      exact (order48_no_normal_subgroup_card_six hG hSyl A) hAcard |>.elim
    · exact hQfour
  exact ⟨z, hzK, hz2, hzcenter, hQcard, hQsyl,
    order24_classification_of_card_sylow_three_eq_four hQcard hQsyl⟩

/-- The action-kernel reduction therefore always supplies a central
involution whose order-`24` quotient remains in the four-Sylow-three branch
and is covered by the completed order-`24` classification. -/
theorem order48_four_sylow_three_order24_reduction [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4) :
    ∃ ψ : G →* Equiv.Perm (Fin 4),
      ((Nat.card ψ.ker = 2 ∧
          Nonempty (G ⧸ ψ.ker ≃* Equiv.Perm (Fin 4))) ∨
        (Nat.card ψ.ker = 4 ∧
          Nonempty (G ⧸ ψ.ker ≃* alternatingGroup (Fin 4)))) ∧
      ∃ z : G, z ∈ ψ.ker ∧ orderOf z = 2 ∧
        ∃ hzcenter : z ∈ Subgroup.center G,
          letI := normal_of_le_center (Subgroup.zpowers_le.mpr hzcenter)
          Nat.card (G ⧸ Subgroup.zpowers z) = 24 ∧
          Nat.card (Sylow 3 (G ⧸ Subgroup.zpowers z)) = 4 ∧
          (Nonempty ((G ⧸ Subgroup.zpowers z) ≃* order24_RM) ∨
            Nonempty ((G ⧸ Subgroup.zpowers z) ≃* order24_RN) ∨
            Nonempty ((G ⧸ Subgroup.zpowers z) ≃* order24_RO)) := by
  obtain ⟨ψ, hnormalizes, hψ⟩ :=
    order48_four_sylow_three_extension_cases hG hSyl
  refine ⟨ψ, hψ, ?_⟩
  rcases hψ with h2 | h4
  · exact order48_central_kernel_reduction_to_order24 hG hSyl ψ.ker
      (normal_subgroup_card_two_le_center ψ.ker h2.1) (Or.inl h2.1)
  · exact order48_central_kernel_reduction_to_order24 hG hSyl ψ.ker
      (normal_subgroup_card_four_A4_quotient_le_center_of_normalizes_sylow
        hG ψ.ker h4.1 h4.2 hnormalizes) (Or.inr h4.1)

end Smallgroups.UsefulTheorems
