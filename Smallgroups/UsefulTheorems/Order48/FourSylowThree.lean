/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.Sylow

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

end Smallgroups.UsefulTheorems
