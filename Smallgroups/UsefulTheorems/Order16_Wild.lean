/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.OrderP4_Abel
import Smallgroups.UsefulTheorems.OrderP4_NonAbel
import Smallgroups.UsefulTheorems.CenterInvariant
import Smallgroups.UsefulTheorems.PrimeOrderClassification
import Smallgroups.UsefulTheorems.PrimeSqClassification
import Smallgroups.UsefulTheorems.Counting
import Smallgroups.UsefulTheorems.Order16
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement

/-!
# Classification of groups of order 16 via cyclic extensions (Wild 2005)

Following Marcel Wild's "The Groups of Order Sixteen Made Easy" (AMM, 2005),
we classify groups of order 16 using **cyclic extensions**.

## The key structural insight (Lemma 2 of Wild)

Every group G of order 16 not isomorphic to (C₂)⁴ has a normal subgroup
of order 8 isomorphic to C₈ or K₈ (= C₄ × C₂).  Thus G is built as an extension
(N, 2, τ, v) where τ ∈ Aut(N) with τ² = id, and v ∈ N satisfies τ(v) = v.

## The approach

1. **Lemma 2**: Every non-(C₂)⁴ group of order 16 has a normal C₈ or K₈.
2. **Extension type enumeration**: From Aut(C₈) ≅ K₄ (4 involutions) and
   Aut(K₈) ≅ D₈ (4 conjugacy classes of involutions), we get 6 + 7 = 13
   extension types, plus G₀ = (C₂)⁴.
3. **Realization and distinction**: Each type gives a concrete group;
   element orders and commutativity distinguish them.

## The 14 groups (Wild numbering)

- G₀ = (C₂)⁴ (the "outsider", all elements of order ≤ 2)
- G₁ = C₈ × C₂ … (C₈, 2, id, e)
- G₂ = SD₁₆ = C₈⋊₃C₂ … (C₈, 2, φ₂, e) — semidihedral
- G₃ = C₈⋊₅C₂ … (C₈, 2, φ₃, e)
- G₄ = D₁₆ = C₈⋊₇C₂ … (C₈, 2, φ₄, e) — dihedral
- G₅ = Q₁₆ … (C₈, 2, φ₄, x⁴) — generalized quaternion
- G₆ = C₁₆ … (C₈, 2, id, x) — cyclic
- G₇ = K₄ × C₄ … (K₈, 2, ψ₁, e)
- G₈ = D₈ × C₂ … (K₈, 2, ψ₃, e)
- G₉ = K₄⋊C₄ … (K₈, 2, ψ₅, e)
- G₁₀ = Q₈⋊C₂ … (K₈, 2, ψ₆, e)
- G₁₁ = Q₈ × C₂ … (K₈, 2, ψ₃, x²)
- G₁₂ = C₄⋊C₄ … (K₈, 2, ψ₅, x²)
- G₁₃ = C₄ × C₄ … (K₈, 2, ψ₁, y)

## Main results

* `lemma_normal_c8_or_k8` — Lemma 2: every non-(C₂)⁴ group of order 16 has a normal C₈ or K₈
* `order16_wild_reps` — the 14 concrete representatives
* `order16_wild_classification` — every group of order 16 is isomorphic to one of the 14
* `order16_wild_distinct` — the 14 are pairwise non-isomorphic
-/


namespace Smallgroups.UsefulTheorems

open SemidirectProduct
open Subgroup
open scoped Pointwise

/-! ### C₈ and K₈: type abbreviations and basic properties -/

/-- Cyclic group of order 8 (multiplicative). -/
abbrev C8g : Type := Multiplicative (ZMod 8)

/-- The Klein-8 group C₄ × C₂ ≅ `⟨x, y | x⁴ = y² = 1, xy = yx⟩`. -/
abbrev K8g : Type := Multiplicative (ZMod 4) × Multiplicative (ZMod 2)

instance : Group C8g := inferInstance
instance : Group K8g := inferInstance
instance : CommGroup C8g := inferInstance
instance : CommGroup K8g := inferInstance

@[simp] theorem card_C8g : Nat.card C8g = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

@[simp] theorem card_K8g : Nat.card K8g = 8 := by
  simp [K8g]

/-- Generator of C₈: `Multiplicative.ofAdd (1 : ZMod 8)`. -/
def xC8 : C8g := Multiplicative.ofAdd 1

theorem orderOf_xC8 : orderOf (xC8 : C8g) = 8 := by
  unfold xC8
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- Generators of K₈: `x` of order 4 and `y` of order 2, commuting. -/
def xK8 : K8g := (Multiplicative.ofAdd 1, 1)

def yK8 : K8g := (1, Multiplicative.ofAdd 1)

theorem orderOf_xK8 : orderOf (xK8 : K8g) = 4 := by
  dsimp [xK8]
  rw [Prod.orderOf_mk]
  have h1 : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have h2 : orderOf (1 : Multiplicative (ZMod 2)) = 1 := by simp
  rw [h1, h2]
  simp

theorem orderOf_yK8 : orderOf (yK8 : K8g) = 2 := by
  dsimp [yK8]
  rw [Prod.orderOf_mk]
  have h1 : orderOf (1 : Multiplicative (ZMod 4)) = 1 := by simp
  have h2 : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  rw [h1, h2]
  simp

theorem xK8_sq_ne_one : xK8 ^ 2 ≠ 1 := by
  have hord : orderOf (xK8 : K8g) = 4 := orderOf_xK8
  intro hsq
  have hsq' : (xK8 : K8g) ^ 2 = 1 := hsq
  have hdvd : orderOf (xK8 : K8g) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hsq'
  rw [hord] at hdvd
  omega

/-! ### Automorphisms of C₈

`Aut(C₈) ≅ (Z/8Z)ˣ ≅ K₄`. The four involutive automorphisms
φ₁ (id), φ₂ (x ↦ x³), φ₃ (x ↦ x⁵), φ₄ (x ↦ x⁷)
correspond to multiplication by the units 1, 3, 5, 7 of Z/8Z.

We use `unitAut` and `zmod8_unit_*` from `Order16.lean`.
-/

noncomputable def zmod8_unit_7 : (ZMod 8)ˣ :=
  IsUnit.unit (by decide : IsUnit (7 : ZMod 8))

@[simp] theorem zmod8_unit_7_sq : zmod8_unit_7 ^ 2 = 1 := by
  unfold zmod8_unit_7; decide

/-- The automorphism φ₂: x ↦ x³ on C₈. -/
noncomputable def phi2 : MulAut C8g := unitAut 8 zmod8_unit_3

/-- The automorphism φ₃: x ↦ x⁵ on C₈. -/
noncomputable def phi3 : MulAut C8g := unitAut 8 zmod8_unit_5

/-- The automorphism φ₄: x ↦ x⁷ on C₈ (inversion). -/
noncomputable def phi4 : MulAut C8g := unitAut 8 zmod8_unit_7

@[simp] theorem phi2_sq : phi2 ^ 2 = 1 := by
  unfold phi2; rw [← MonoidHom.map_pow, zmod8_unit_3_sq]; simp

@[simp] theorem phi3_sq : phi3 ^ 2 = 1 := by
  unfold phi3; rw [← MonoidHom.map_pow, zmod8_unit_5_sq]; simp

@[simp] theorem phi4_sq : phi4 ^ 2 = 1 := by
  unfold phi4; rw [← MonoidHom.map_pow, zmod8_unit_7_sq]; simp

/-! ### Automorphisms of K₈ (= C₄ × C₂)

`Aut(K₈) ≅ D₈`.  The eight automorphisms from Fact 4 of Wild.
Working multiplicatively on `K8g = Multiplicative (ZMod 4) × Multiplicative (ZMod 2)`,
the four involutive conjugacy classes are:

* ψ₁ = id:        (x, y) ↦ (x, y)
* ψ₃:             (x, y) ↦ (x⁻¹, y)
* ψ₅:             (x, y) ↦ (x, π(x) * y)  where π : C₄ → C₂ is the natural projection
* ψ₆:             (x, y) ↦ (x⁻¹, π(x) * y)

All four satisfy ψ² = id.
-/

/-- The natural projection `Multiplicative (ZMod 4) → Multiplicative (ZMod 2)`
sending `ofAdd a` to `ofAdd (a mod 2)`. This is a group homomorphism. -/
noncomputable def k8Proj : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (ZMod.cast (Multiplicative.toAdd x) : ZMod 2)
  map_one' := by simp
  map_mul' x y := by
    simp [toAdd_mul, ZMod.cast_add]

theorem k8Proj_sq (x : Multiplicative (ZMod 4)) : (k8Proj x) ^ 2 = 1 := by
  have hcard : Fintype.card (Multiplicative (ZMod 2)) = 2 := by simp
  have h := pow_card_eq_one (x := k8Proj x)
  rw [hcard] at h
  exact h

/-- ψ₁ = identity on K₈. -/
def psi1 : MulAut K8g := MulEquiv.refl _

/-- ψ₃: x ↦ x⁻¹, y ↦ y.  Additively: (a,b) ↦ (-a, b). -/
noncomputable def psi3 : MulAut K8g where
  toFun p := (p.1⁻¹, p.2)
  invFun p := (p.1⁻¹, p.2)
  left_inv p := by rcases p with ⟨x, y⟩; simp
  right_inv p := by rcases p with ⟨x, y⟩; simp
  map_mul' p q := by
    rcases p with ⟨x₁, y₁⟩
    rcases q with ⟨x₂, y₂⟩
    simp [mul_inv_rev, mul_comm]

@[simp] theorem k8Proj_self_mul (x : Multiplicative (ZMod 4)) : k8Proj x * k8Proj x = 1 := by
  rw [← sq, k8Proj_sq x]

@[simp] theorem k8Proj_inv (x : Multiplicative (ZMod 4)) : (k8Proj x)⁻¹ = k8Proj x := by
  apply inv_eq_iff_mul_eq_one.mpr
  rw [k8Proj_self_mul x]

/-- ψ₅: x ↦ xy, y ↦ y.  Additively: (a,b) ↦ (a, c(a)+b). -/
noncomputable def psi5 : MulAut K8g where
  toFun p := (p.1, k8Proj p.1 * p.2)
  invFun p := (p.1, (k8Proj p.1)⁻¹ * p.2)
  left_inv p := by
    rcases p with ⟨x, y⟩; dsimp
    calc
      (x, (k8Proj x)⁻¹ * (k8Proj x * y)) = (x, ((k8Proj x)⁻¹ * k8Proj x) * y) := by group
      _ = (x, 1 * y) := by simp
      _ = (x, y) := by simp
  right_inv p := by
    rcases p with ⟨x, y⟩; dsimp
    calc
      (x, k8Proj x * ((k8Proj x)⁻¹ * y)) = (x, (k8Proj x * (k8Proj x)⁻¹) * y) := by group
      _ = (x, 1 * y) := by simp
      _ = (x, y) := by simp
  map_mul' p q := by
    rcases p with ⟨x₁, y₁⟩; rcases q with ⟨x₂, y₂⟩
    apply Prod.ext
    · rfl
    · simp [k8Proj.map_mul, mul_assoc, mul_left_comm, mul_comm]

/-- ψ₆: x ↦ x³, y ↦ x²y.  Additively: (a,b) ↦ (-a, c(a)+b). -/
noncomputable def psi6 : MulAut K8g where
  toFun p := (p.1⁻¹, k8Proj p.1 * p.2)
  invFun p := (p.1⁻¹, (k8Proj p.1)⁻¹ * p.2)
  left_inv p := by
    rcases p with ⟨x, y⟩; dsimp
    rw [k8Proj.map_inv x]
    apply Prod.ext
    · simp
    · simp [← mul_assoc, k8Proj_self_mul x]
  right_inv p := by
    rcases p with ⟨x, y⟩; dsimp
    apply Prod.ext
    · simp
    · dsimp
      rw [k8Proj.map_inv]
      simp [← mul_assoc, k8Proj_self_mul x]
  map_mul' p q := by
    rcases p with ⟨x₁, y₁⟩; rcases q with ⟨x₂, y₂⟩
    apply Prod.ext
    · simp [mul_inv_rev, mul_comm]
    · simp [k8Proj.map_mul, mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem psi1_sq : psi1 ^ 2 = 1 := by
  unfold psi1; apply MulEquiv.ext; intro x; rfl

@[simp] theorem psi3_sq : psi3 ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  rcases p with ⟨x, y⟩
  calc
    (psi3 ^ 2) (x, y) = psi3 (psi3 (x, y)) := rfl
    _ = psi3 (x⁻¹, y) := rfl
    _ = ((x⁻¹)⁻¹, y) := rfl
    _ = (x, y) := by simp

@[simp] theorem psi5_sq : psi5 ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  rcases p with ⟨x, y⟩
  calc
    (psi5 ^ 2) (x, y) = psi5 (psi5 (x, y)) := rfl
    _ = psi5 (x, k8Proj x * y) := rfl
    _ = (x, k8Proj x * (k8Proj x * y)) := rfl
    _ = (x, (k8Proj x * k8Proj x) * y) := by group
    _ = (x, (k8Proj x ^ 2) * y) := by rw [sq]
    _ = (x, 1 * y) := by rw [k8Proj_sq x]
    _ = (x, y) := by simp

@[simp] theorem psi6_sq : psi6 ^ 2 = 1 := by
  apply MulEquiv.ext
  intro p
  rcases p with ⟨x, y⟩
  calc
    (psi6 ^ 2) (x, y) = psi6 (psi6 (x, y)) := rfl
    _ = psi6 (x⁻¹, k8Proj x * y) := rfl
    _ = ((x⁻¹)⁻¹, k8Proj (x⁻¹) * (k8Proj x * y)) := rfl
    _ = (x, k8Proj (x⁻¹) * (k8Proj x * y)) := by simp
    _ = (x, ((k8Proj x)⁻¹ * (k8Proj x * y))) := by rw [k8Proj.map_inv]
    _ = (x, (((k8Proj x)⁻¹ * k8Proj x) * y)) := by group
    _ = (x, 1 * y) := by simp
    _ = (x, y) := by simp

/-! ### C₂ → Aut(N) maps for building semidirect products -/

private lemma c2_two_cases (a : Multiplicative (ZMod 2)) : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  have := show ∀ a : Multiplicative (ZMod 2), a = 1 ∨ a = Multiplicative.ofAdd 1 from by decide
  exact this a

@[simp] private lemma c2_mul_self : (Multiplicative.ofAdd (1 : ZMod 2)
* Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 := by
  decide

set_option linter.flexible false in
/-- C₂-action on C₈ via φ₂ (x ↦ x³). -/
noncomputable def c2Action_phi2 : Multiplicative (ZMod 2) →* MulAut C8g where
  toFun g := if g = 1 then 1 else phi2
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, phi2_sq]

set_option linter.flexible false in
/-- C₂-action on C₈ via φ₃ (x ↦ x⁵). -/
noncomputable def c2Action_phi3 : Multiplicative (ZMod 2) →* MulAut C8g where
  toFun g := if g = 1 then 1 else phi3
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, phi3_sq]

set_option linter.flexible false in
/-- C₂-action on C₈ via φ₄ (x ↦ x⁷). -/
noncomputable def c2Action_phi4 : Multiplicative (ZMod 2) →* MulAut C8g where
  toFun g := if g = 1 then 1 else phi4
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, phi4_sq]

set_option linter.flexible false in
/-- C₂-action on K₈ via ψ₃. -/
noncomputable def c2Action_psi3 : Multiplicative (ZMod 2) →* MulAut K8g where
  toFun g := if g = 1 then 1 else psi3
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, psi3_sq]

set_option linter.flexible false in
/-- C₂-action on K₈ via ψ₅. -/
noncomputable def c2Action_psi5 : Multiplicative (ZMod 2) →* MulAut K8g where
  toFun g := if g = 1 then 1 else psi5
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, psi5_sq]

set_option linter.flexible false in
/-- C₂-action on K₈ via ψ₆. -/
noncomputable def c2Action_psi6 : Multiplicative (ZMod 2) →* MulAut K8g where
  toFun g := if g = 1 then 1 else psi6
  map_one' := by simp
  map_mul' a b := by
    rcases c2_two_cases a with (rfl|rfl) <;> rcases c2_two_cases b with (rfl|rfl) <;>
      simp [c2_mul_self]; try rw [← sq, psi6_sq]

/-! ### The 14 concrete groups

We define each group in order, matching the algebraic descriptions from Wild.

**Six groups from C₈-extensions:**
-/

/-- G₁ = C₈ × C₂. -/
noncomputable abbrev order16_wild_G1 : Type := C8g × Multiplicative (ZMod 2)

/-- G₂ = SD₁₆ = C₈ ⋊₃ C₂ (semidihedral). -/
noncomputable abbrev order16_wild_G2 : Type :=
  SemidirectProduct C8g (Multiplicative (ZMod 2)) c2Action_phi2

/-- G₃ = C₈ ⋊₅ C₂. -/
noncomputable abbrev order16_wild_G3 : Type :=
  SemidirectProduct C8g (Multiplicative (ZMod 2)) c2Action_phi3

/-- G₄ = D₁₆ = C₈ ⋊₇ C₂ (dihedral). -/
noncomputable abbrev order16_wild_G4 : Type :=
  SemidirectProduct C8g (Multiplicative (ZMod 2)) c2Action_phi4

/-- G₅ = Q₁₆ (generalized quaternion). -/
noncomputable abbrev order16_wild_G5 : Type := QuaternionGroup 4

/-- G₆ = C₁₆ (cyclic). -/
noncomputable abbrev order16_wild_G6 : Type := order16_A1

/-! **Seven groups from K₈-extensions:** -/

/-- G₇ = K₄ × C₄. -/
noncomputable abbrev order16_wild_G7 : Type := K8g × Multiplicative (ZMod 2)

/-- G₈ = D₈ × C₂. -/
noncomputable abbrev order16_wild_G8 : Type :=
  SemidirectProduct K8g (Multiplicative (ZMod 2)) c2Action_psi3

/-- G₉ = K₄ ⋊ C₄. -/
noncomputable abbrev order16_wild_G9 : Type :=
  SemidirectProduct K8g (Multiplicative (ZMod 2)) c2Action_psi5

/-- G₁₀ = Q₈ ⋊ C₂. -/
noncomputable abbrev order16_wild_G10 : Type :=
  SemidirectProduct K8g (Multiplicative (ZMod 2)) c2Action_psi6

/-- G₁₁ = Q₈ × C₂. -/
noncomputable abbrev order16_wild_G11 : Type := QuaternionGroup 2 × Multiplicative (ZMod 2)

/-- G₁₂ = C₄ ⋊ C₄ (semidirect product of C₄ by C₄ via inversion `x ↦ x⁻¹`).
We reuse the definition from `Order16.lean`. -/
noncomputable abbrev order16_wild_G12 : Type := order16_N3

/-- G₁₃ = C₄ × C₄. -/
noncomputable abbrev order16_wild_G13 : Type := order16_A3

/-- G₀ = (C₂)⁴ (the "outsider"). -/
noncomputable abbrev order16_wild_G0 : Type := order16_A5

/-! ### Cardinalities -/

@[simp] theorem card_order16_wild_G0 : Nat.card order16_wild_G0 = 16 := card_order16_A5
@[simp] theorem card_order16_wild_G1 : Nat.card order16_wild_G1 = 16 := by simp
@[simp] theorem card_order16_wild_G2 : Nat.card order16_wild_G2 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G3 : Nat.card order16_wild_G3 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G4 : Nat.card order16_wild_G4 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G5 : Nat.card order16_wild_G5 = 16 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
@[simp] theorem card_order16_wild_G6 : Nat.card order16_wild_G6 = 16 := card_order16_A1
@[simp] theorem card_order16_wild_G7 : Nat.card order16_wild_G7 = 16 := by simp
@[simp] theorem card_order16_wild_G8 : Nat.card order16_wild_G8 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G9 : Nat.card order16_wild_G9 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G10 : Nat.card order16_wild_G10 = 16 := by
  rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G11 : Nat.card order16_wild_G11 = 16 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]; simp
@[simp] theorem card_order16_wild_G12 : Nat.card order16_wild_G12 = 16 := by
  dsimp [order16_wild_G12, order16_N3]; rw [SemidirectProduct.card]; simp
@[simp] theorem card_order16_wild_G13 : Nat.card order16_wild_G13 = 16 := card_order16_A3

/-! ### The full list of 14 representatives -/

/-- The 14 isomorphism classes of groups of order 16 (Wild numbering). -/
noncomputable abbrev order16_wild_reps : Fin 14 → Type
  | 0 => order16_wild_G0
  | 1 => order16_wild_G1
  | 2 => order16_wild_G2
  | 3 => order16_wild_G3
  | 4 => order16_wild_G4
  | 5 => order16_wild_G5
  | 6 => order16_wild_G6
  | 7 => order16_wild_G7
  | 8 => order16_wild_G8
  | 9 => order16_wild_G9
  | 10 => order16_wild_G10
  | 11 => order16_wild_G11
  | 12 => order16_wild_G12
  | 13 => order16_wild_G13

noncomputable instance instGroupOrder16WildReps (i : Fin 14) : Group (order16_wild_reps i) :=
  match i with
  | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
  | 4 => inferInstance | 5 => inferInstance | 6 => inferInstance | 7 => inferInstance
  | 8 => inferInstance | 9 => inferInstance | 10 => inferInstance | 11 => inferInstance
  | 12 => inferInstance | 13 => inferInstance

/-- Each representative has order 16. -/
theorem card_order16_wild_reps (i : Fin 14) : Nat.card (order16_wild_reps i) = 16 := by
  fin_cases i <;>
    first
    | exact card_order16_wild_G0
    | exact card_order16_wild_G1
    | exact card_order16_wild_G2
    | exact card_order16_wild_G3
    | exact card_order16_wild_G4
    | exact card_order16_wild_G5
    | exact card_order16_wild_G6
    | exact card_order16_wild_G7
    | exact card_order16_wild_G8
    | exact card_order16_wild_G9
    | exact card_order16_wild_G10
    | exact card_order16_wild_G11
    | exact card_order16_wild_G12
    | exact card_order16_wild_G13

/-! ### Lemma 2: Every non-(C₂)⁴ group of order 16 has a normal C₈ or K₈ -/

/-- Lemma 2 of Wild:
If G is a group of order 16 not isomorphic to (C₂)⁴, then G has a normal subgroup
of order 8 isomorphic to C₈ or to K₈. -/
theorem lemma_normal_c8_or_k8 {G : Type*} [Group G]
    (hcard : Nat.card G = 16)
    (h_not_elem : ¬ Nonempty (G ≃* order16_wild_G0)) :
    (∃ (H : Subgroup G), H.Normal ∧ Nat.card H = 8 ∧
      Nonempty (H ≃* C8g)) ∨
    (∃ (H : Subgroup G), H.Normal ∧ Nat.card H = 8 ∧
      Nonempty (H ≃* K8g)) := by
  classical
  have hcard' : Nat.card G ≠ 0 := by rw [hcard]; norm_num
  haveI : Finite G := by
    by_contra hinf
    haveI : Infinite G := ⟨hinf⟩
    have hcard0 : Nat.card G = 0 := Nat.card_eq_zero_of_infinite
    exact hcard' hcard0
  haveI : Fintype G := Fintype.ofFinite G
  -- If G has an element of order 8, then H = ⟨x⟩ ≅ C₈ is normal (index 2).
  by_cases h_ord8 : ∃ g : G, orderOf g = 8
  · rcases h_ord8 with ⟨g, hg⟩
    let H : Subgroup G := zpowers g
    have hHcard : Nat.card H = 8 := by rw [Nat.card_zpowers, hg]
    have hHindex : H.index = 2 := by
      have hmul := H.card_mul_index
      rw [hHcard, hcard] at hmul
      omega
    have hHnorm : H.Normal := normal_of_index_eq_two hHindex
    have hH_iso : Nonempty (H ≃* C8g) := by
      haveI : IsCyclic H := isCyclic_zpowers g
      have hcard_H : Fintype.card H = 8 := by
        rw [← Nat.card_eq_fintype_card, hHcard]
      have hcard_C8 : Fintype.card C8g = 8 := by
        rw [← Nat.card_eq_fintype_card, card_C8g]
      -- Two cyclic groups of the same finite order are isomorphic
      apply Nonempty.intro
      -- This follows from the classification of cyclic groups
      sorry
    exact Or.inl ⟨H, hHnorm, hHcard, hH_iso⟩
  · -- No element of order 8.  The full proof would use the center argument
    -- (Fact 6: p-group has nontrivial center) and case analysis on elements
    -- of order 4 to find K8.  We state the result as a sorry for now.
    sorry

/-! ### Main classification theorem

We state that every group of order 16 is isomorphic to one of the 14 representatives,
and that they are pairwise non-isomorphic.  Full proofs are deferred; the file provides
the structural framework following Wild's approach.
-/

/-- **Completeness.** Every group of order 16 is isomorphic to one of the 14 representatives. -/
theorem order16_wild_classification {G : Type*} [Group G]
    (hcard : Nat.card G = 16) : ∃ i : Fin 14, Nonempty (G ≃* order16_wild_reps i) := by
  sorry

/-- **Distinctness.** The 14 representatives are pairwise non-isomorphic. -/
theorem order16_wild_distinct {i j : Fin 14}
    (h : Nonempty (order16_wild_reps i ≃* order16_wild_reps j)) : i = j := by
  sorry

/-- The 14 representatives are pairwise non-isomorphic (the `IsClassif` form). -/
theorem order16_wild_pairwise_noniso : PairwiseNonMulEquiv order16_wild_reps := by
  intro i j hiso
  exact order16_wild_distinct hiso

set_option linter.unusedVariables false in
/-- There are exactly 14 groups of order 16. -/
theorem order16_wild_isClassif : IsClassif 16 order16_wild_reps :=
  { card := card_order16_wild_reps
    complete := fun G _ hG => order16_wild_classification hG
    distinct := fun i j h => order16_wild_distinct h
  }

end Smallgroups.UsefulTheorems
