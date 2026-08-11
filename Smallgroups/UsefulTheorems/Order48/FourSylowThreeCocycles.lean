/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order48.FourSylowThreeReps

/-!
# Cocycle reduction for the order-48 four-Sylow-three branch

Every group in this branch has a central involution whose quotient is one of
the three order-24 groups in the four-Sylow-three branch.  The general central
extension reconstruction theorem therefore reduces exhaustiveness to
normalized `ZMod 2`-valued cocycles over `order24_RM`, `order24_RN`, and
`order24_RO`.
-/

namespace Smallgroups.UsefulTheorems

variable {G : Type*} [Group G]

/-- Every order-48 group with four Sylow `3`-subgroups is a central cocycle
group over one of the three possible order-24 quotients. -/
theorem order48_four_sylow_three_cocycle_reduction [Finite G]
    (hG : Nat.card G = 48) (hSyl : Nat.card (Sylow 3 G) = 4) :
    (∃ (f : order24_RM → order24_RM → ZMod 2) (hf : IsCentralCocycle f),
      Nonempty (G ≃* CocycleGroup f hf)) ∨
    (∃ (f : order24_RN → order24_RN → ZMod 2) (hf : IsCentralCocycle f),
      Nonempty (G ≃* CocycleGroup f hf)) ∨
    (∃ (f : order24_RO → order24_RO → ZMod 2) (hf : IsCentralCocycle f),
      Nonempty (G ≃* CocycleGroup f hf)) := by
  obtain ⟨ψ, _, z, _, hz2, hzcenter, _, _, hquot⟩ :=
    order48_four_sylow_three_order24_reduction hG hSyl
  letI : (Subgroup.zpowers z).Normal :=
    normal_of_le_center (Subgroup.zpowers_le.mpr hzcenter)
  rcases hquot with hRM | hRN | hRO
  · obtain ⟨e⟩ := hRM
    exact Or.inl (cocycleGroup_reconstruction_of_quotient_iso hzcenter hz2 e)
  · obtain ⟨e⟩ := hRN
    exact Or.inr (Or.inl
      (cocycleGroup_reconstruction_of_quotient_iso hzcenter hz2 e))
  · obtain ⟨e⟩ := hRO
    exact Or.inr (Or.inr
      (cocycleGroup_reconstruction_of_quotient_iso hzcenter hz2 e))

end Smallgroups.UsefulTheorems
