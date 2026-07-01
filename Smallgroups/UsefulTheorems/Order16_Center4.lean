/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order16
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Groups of order 16 with center ≅ C4

There are exactly **2** non-abelian groups of order 16 whose center is a cyclic group
of order 4: the modular maximal-cyclic group `C8 ⋊₅ C2` (defined as `order16_N1`)
and `Q8 ⋊ C2` (currently a placeholder `order16_N2`).

## Main results

* `order16_N1_classification` — a 16-group with center C4 and an element of order 8 is `order16_N1`
* `order16_N2_classification` — (future) a 16-group
with center C4 and no element of order 8 is `order16_N2`
-/

namespace Smallgroups.UsefulTheorems

open SemidirectProduct
open Subgroup

/-! ### Characterization of `order16_N1` (C8 ⋊₅ C2)

Among the two 16-groups with center C4, only `order16_N1` contains an element of order 8.
-/

/-- A group of order 16 with center ≅ C4 and containing an element of order 8 is isomorphic to
`order16_N1` (C8 ⋊₅ C2 via `x ↦ x⁵`). -/
theorem order16_N1_classification {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 16)
    (hcenter : Nonempty (center G ≃* CyclicRep 4))
    (hord8 : ∃ g : G, orderOf g = 8) :
    Nonempty (G ≃* order16_N1) := by
  rcases hord8 with ⟨g, hg⟩
  have hg8 : g ^ 8 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  let H : Subgroup G := Subgroup.zpowers g
  have hHcard : Nat.card H = 8 := by rw [Nat.card_zpowers, hg]
  have hHindex : H.index = 2 := by
    have hmul := H.card_mul_index; rw [hHcard, hcard] at hmul; omega
  haveI hHnorm : H.Normal := Subgroup.normal_of_index_eq_two hHindex
  have hZCcard : Nat.card (center G) = 4 := by
    rcases hcenter with ⟨hc⟩
    have hc4 : Nat.card (CyclicRep 4) = 4 := card_cyclicRep (by norm_num : 4 ≠ 0)
    rw [← hc4, ← Nat.card_congr hc.toEquiv]

  -- Proof strategy: show Z(G) = ⟨g²⟩ ≤ H, pick t ∉ H with t·g·t⁻¹ = g⁵,
  -- find s with s² = 1 and s·g·s⁻¹ = g⁵, then build isomorphism to C8 ⋊₅ C2.
  sorry

end Smallgroups.UsefulTheorems
