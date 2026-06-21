/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PSq
import Smallgroups.UsefulTheorems.PrimeSqClassification

/-!
# Exhaustiveness for order `2 p²`: the reduction to an involution

Every group of order `2 p²` (`p` an odd prime) is a semidirect product `N ⋊[ψ] ℤ/2` with `N` the
abelian Sylow-`p` subgroup (order `p²`, so `≅ ℤ/p²` or `(ℤ/p)²`). This file establishes that
reduction; classifying the involution `ψ(1) ∈ Aut N` then distributes `G` among the five
representatives (the remaining step).
-/

namespace Smallgroups.UsefulTheorems

variable {G : Type*} [Group G] {p : ℕ}

/-- **Reduction.** A group of order `2 p²` (`p ≠ 2` prime) is a semidirect product of `ℤ/p²` or
`(ℤ/p)²` by `ℤ/2`. -/
theorem order2psq_semidirect [Fact p.Prime] (hp2 : p ≠ 2) [Finite G]
    (hG : Nat.card G = 2 * p ^ 2) :
    (∃ φ : Multiplicative (ZMod 2) →* MulAut (CyclicRep (p ^ 2)),
        Nonempty (G ≃* SemidirectProduct (CyclicRep (p ^ 2)) (Multiplicative (ZMod 2)) φ)) ∨
      (∃ φ : Multiplicative (ZMod 2) →* MulAut (ElemAbelianRep p),
        Nonempty (G ≃* SemidirectProduct (ElemAbelianRep p) (Multiplicative (ZMod 2)) φ)) := by
  have hp : p.Prime := Fact.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, K, φ, _, hPcard, hKcard, ⟨e⟩⟩ :=
    psq_semidirectProduct hp Nat.prime_two hp2 (by simpa using hp.ne_one) (by rw [hG]; ring)
  have eK : (K : Type _) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hKcard (by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  rcases prime_sq_classification (G := (P : Type _)) hPcard with hP | hP
  · exact Or.inl ⟨_, ⟨e.trans (SemidirectProduct.congr' hP.some eK)⟩⟩
  · exact Or.inr ⟨_, ⟨e.trans (SemidirectProduct.congr' hP.some eK)⟩⟩

end Smallgroups.UsefulTheorems
