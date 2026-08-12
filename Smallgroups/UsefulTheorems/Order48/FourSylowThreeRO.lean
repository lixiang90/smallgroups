/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeRN

/-!
# The RO reduction

The RO quotient is `S₄`.  Its normal Klein four subgroup is not a Hall
subgroup, so the RM/RN semidirect reduction does not apply directly.  The
available conjugation-action analysis instead gives the two possible central
extension shapes: a central `C₂` over `S₄`, or a central order-`4` kernel over
`A₄`.  This file packages that reduction for arbitrary cocycles over RO.
-/

namespace Smallgroups.UsefulTheorems

theorem order48_RO_cocycle_reduction_to_typed_extension
    (f : order24_RO → order24_RO → ZMod 2) (hf : IsCentralCocycle f) :
    ∃ ψ : CocycleGroup f hf →* Equiv.Perm (Fin 4),
      (Nonempty (ψ.ker ≃* CyclicRep 2) ∧
          ψ.ker ≤ Subgroup.center (CocycleGroup f hf) ∧
          Nonempty ((CocycleGroup f hf) ⧸ ψ.ker ≃* Equiv.Perm (Fin 4))) ∨
      (((Nonempty (ψ.ker ≃* CyclicRep (2 ^ 2)) ∨
          Nonempty (ψ.ker ≃* ElemAbelianRep 2)) ∧
        ψ.ker ≤ Subgroup.center (CocycleGroup f hf)) ∧
        Nonempty ((CocycleGroup f hf) ⧸ ψ.ker ≃*
          alternatingGroup (Fin 4))) := by
  obtain ⟨hcard, hsyl⟩ := order48_RO_cocycle_card_and_sylow_three f hf
  exact order48_four_sylow_three_typed_extension_cases hcard hsyl

/-- The typed RO extension reduction supplies a central involution whose
order-`24` quotient is again one of the three four-Sylow-`3` quotients.  This
is the recursive reduction used before the final `S₄` extension orbit split. -/
theorem order48_RO_cocycle_typed_extension_has_central_involution_reduction
    (f : order24_RO → order24_RO → ZMod 2)
    (hf : IsCentralCocycle f) :
    ∃ ψ : CocycleGroup f hf →* Equiv.Perm (Fin 4),
      ∃ z : CocycleGroup f hf,
        z ∈ ψ.ker ∧ orderOf z = 2 ∧
        ∃ hzcenter : z ∈ Subgroup.center (CocycleGroup f hf),
          letI := normal_of_le_center
            (Subgroup.zpowers_le.mpr hzcenter)
          Nat.card ((CocycleGroup f hf) ⧸ Subgroup.zpowers z) = 24 ∧
          Nat.card (Sylow 3 ((CocycleGroup f hf) ⧸ Subgroup.zpowers z)) = 4 ∧
          (Nonempty (((CocycleGroup f hf) ⧸ Subgroup.zpowers z) ≃* order24_RM) ∨
            Nonempty (((CocycleGroup f hf) ⧸ Subgroup.zpowers z) ≃* order24_RN) ∨
            Nonempty (((CocycleGroup f hf) ⧸ Subgroup.zpowers z) ≃* order24_RO)) := by
  obtain ⟨hcard, hsyl⟩ := order48_RO_cocycle_card_and_sylow_three f hf
  obtain ⟨ψ, hψ⟩ := order48_RO_cocycle_reduction_to_typed_extension f hf
  refine ⟨ψ, ?_⟩
  rcases hψ with h2 | h4
  · have hker : Nat.card ψ.ker = 2 := by
      obtain ⟨e⟩ := h2.1
      exact (Nat.card_congr e.toEquiv).trans (card_cyclicRep (by norm_num))
    obtain ⟨z, hzker, hz2, hzcenter, hqcard, hqsyl, hq⟩ :=
      order48_central_kernel_reduction_to_order24 hcard hsyl ψ.ker h2.2.1
        (Or.inl hker)
    exact ⟨z, hzker, hz2, hzcenter, hqcard, hqsyl, hq⟩
  · have hker : Nat.card ψ.ker = 4 := by
      rcases h4.1.1 with hcyc | helem
      · obtain ⟨e⟩ := hcyc
        exact (Nat.card_congr e.toEquiv).trans (card_cyclicRep (by norm_num))
      · obtain ⟨e⟩ := helem
        exact (Nat.card_congr e.toEquiv).trans
          (card_elemAbelianRep (by norm_num : (2 : ℕ) ≠ 0))
    obtain ⟨z, hzker, hz2, hzcenter, hqcard, hqsyl, hq⟩ :=
      order48_central_kernel_reduction_to_order24 hcard hsyl ψ.ker h4.1.2
        (Or.inr hker)
    exact ⟨z, hzker, hz2, hzcenter, hqcard, hqsyl, hq⟩

end Smallgroups.UsefulTheorems
