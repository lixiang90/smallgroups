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
import Mathlib.GroupTheory.NoncommCoprod
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

/-! ### Auxiliary lemmas for Lemma 2 -/

/-- A group in which every element squares to `1` is commutative (Fact 2 of Wild). -/
private lemma mul_comm_of_sq_eq_one {G : Type*} [Group G]
    (h : ∀ g : G, g ^ 2 = 1) (a b : G) : a * b = b * a := by
  have ha_sq' : a * a = 1 := by rw [← pow_two]; exact h a
  have hb_sq' : b * b = 1 := by rw [← pow_two]; exact h b
  have hab_sq' : (a * b) * (a * b) = 1 := by rw [← pow_two]; exact h (a * b)
  have ha_inv : a = a⁻¹ := eq_inv_of_mul_eq_one_left ha_sq'
  have hb_inv : b = b⁻¹ := eq_inv_of_mul_eq_one_left hb_sq'
  have hab_inv : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab_sq'
  calc
    a * b = (a * b)⁻¹ := hab_inv
    _ = b⁻¹ * a⁻¹ := by simp
    _ = b * a := by rw [ha_inv.symm, hb_inv.symm]

/-- In a group of order `16` without elements of order `8`, every element has order
`1`, `2`, or `4`. -/
private lemma orderOf_cases_of_card16 {G : Type*} [Group G]
    (hcard : Nat.card G = 16) (h_ord8 : ¬ ∃ g : G, orderOf g = 8) (g : G) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 4 := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hdvd : orderOf g ∣ 16 := by rw [← hcard]; exact orderOf_dvd_natCard g
  have h_not8 : orderOf g ≠ 8 := fun h => h_ord8 ⟨g, h⟩
  have h_not16 : orderOf g ≠ 16 := by
    intro h16
    exact h_ord8 ⟨g ^ 2, by rw [orderOf_pow g, h16]; norm_num⟩
  have h_mem : orderOf g ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have h_divs : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
  rw [h_divs] at h_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
  omega

/-- Reduce an integer power of a torsion element to a natural power below the torsion bound. -/
private lemma zpow_eq_pow_emod {G : Type*} [Group G] (g : G) {n : ℕ} (hn : 0 < n)
    (hg : g ^ n = 1) (k : ℤ) : g ^ k = g ^ (k % (n : ℤ)).toNat := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have h0 : (0 : ℤ) ≤ k % (n : ℤ) := Int.emod_nonneg k hn'
  calc g ^ k = g ^ ((n : ℤ) * (k / (n : ℤ)) + k % (n : ℤ)) := by
        rw [Int.mul_ediv_add_emod]
    _ = (g ^ (n : ℤ)) ^ (k / (n : ℤ)) * g ^ (k % (n : ℤ)) := by
        rw [zpow_add, zpow_mul]
    _ = g ^ (k % (n : ℤ)) := by
        rw [zpow_natCast, hg, one_zpow, one_mul]
    _ = g ^ (k % (n : ℤ)).toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg h0]

/-- An element of `⟨x⟩` is a natural power `x ^ m` with `m < orderOf x`. -/
private lemma exists_pow_eq_of_mem_zpowers {G : Type*} [Group G] {x y : G}
    (hx : 0 < orderOf x) (h : y ∈ Subgroup.zpowers x) :
    ∃ m : ℕ, m < orderOf x ∧ x ^ m = y := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  refine ⟨(k % (orderOf x : ℤ)).toNat, ?_, ?_⟩
  · have hlt : k % (orderOf x : ℤ) < (orderOf x : ℤ) :=
      Int.emod_lt_of_pos k (by exact_mod_cast hx)
    have h0 : (0 : ℤ) ≤ k % (orderOf x : ℤ) :=
      Int.emod_nonneg k (by exact_mod_cast hx.ne')
    omega
  · rw [← zpow_eq_pow_emod x hx (pow_orderOf_eq_one x) k, hk]

/-- The homomorphism `Multiplicative (ZMod n) →* G` sending `Multiplicative.ofAdd 1` to `g`,
for an element `g` with `g ^ n = 1`. -/
private noncomputable def zmodPowHom {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  AddMonoidHom.toMultiplicativeLeft <| ZMod.lift n
    ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
      rw [zmultiplesHom_apply, ← ofMul_zpow, zpow_natCast, hg, ofMul_one]⟩

private lemma zmodPowHom_apply {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1)
    (k : ℕ) : zmodPowHom n g hg (Multiplicative.ofAdd ((k : ZMod n))) = g ^ k := by
  have h1 : (((k : ℤ)) : ZMod n) = ((k : ZMod n)) := by push_cast; rfl
  simp only [zmodPowHom, AddMonoidHom.toMultiplicativeLeft_apply_apply, toAdd_ofAdd]
  rw [← h1, ZMod.lift_coe]
  rw [zmultiplesHom_apply, ← ofMul_zpow, toMul_ofMul, zpow_natCast]

/-- If `x` has order `4`, `w` has order `2`, `x` and `w` commute, and `w ∉ ⟨x⟩`, then in a
group of order `16` the subgroup generated by `x` and `w` is a normal subgroup of order `8`
isomorphic to `K₈ = C₄ × C₂`. -/
private lemma normal_k8_of_commuting {G : Type*} [Group G] (hcard : Nat.card G = 16)
    (x w : G) (hx4 : orderOf x = 4) (hw2 : orderOf w = 2)
    (hcomm : Commute x w) (hw_notin : w ∉ Subgroup.zpowers x) :
    ∃ H : Subgroup G, H.Normal ∧ Nat.card H = 8 ∧ Nonempty (H ≃* K8g) := by
  classical
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hw2' : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
  let fx : Multiplicative (ZMod 4) →* G := zmodPowHom 4 x hx4'
  let fw : Multiplicative (ZMod 2) →* G := zmodPowHom 2 w hw2'
  have hfx : ∀ a : Multiplicative (ZMod 4), fx a = x ^ (Multiplicative.toAdd a).val := by
    intro a
    have ha : a = Multiplicative.ofAdd (((Multiplicative.toAdd a).val : ZMod 4)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    conv_lhs => rw [ha]
    exact zmodPowHom_apply 4 x hx4' _
  have hfw : ∀ b : Multiplicative (ZMod 2), fw b = w ^ (Multiplicative.toAdd b).val := by
    intro b
    have hb : b = Multiplicative.ofAdd (((Multiplicative.toAdd b).val : ZMod 2)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, ofAdd_toAdd]
    conv_lhs => rw [hb]
    exact zmodPowHom_apply 2 w hw2' _
  have hcomm' : ∀ (a : Multiplicative (ZMod 4)) (b : Multiplicative (ZMod 2)),
      Commute (fx a) (fw b) := by
    intro a b
    rw [hfx a, hfw b]
    exact hcomm.pow_pow _ _
  have hinj : Function.Injective (fx.noncommCoprod fw hcomm') := by
    refine (injective_iff_map_eq_one _).mpr ?_
    rintro ⟨a, b⟩ hab
    simp only [MonoidHom.noncommCoprod_apply] at hab
    rw [hfx a, hfw b] at hab
    have hbv_lt : (Multiplicative.toAdd b).val < 2 := ZMod.val_lt _
    have hav_lt : (Multiplicative.toAdd a).val < 4 := ZMod.val_lt _
    have hbv0 : (Multiplicative.toAdd b).val = 0 := by
      by_contra hbv1
      have hbv1' : (Multiplicative.toAdd b).val = 1 := by omega
      rw [hbv1', pow_one] at hab
      refine hw_notin ?_
      have hw_eq : w = (x ^ (Multiplicative.toAdd a).val)⁻¹ :=
        eq_inv_of_mul_eq_one_right hab
      rw [hw_eq]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
    rw [hbv0, pow_zero, mul_one] at hab
    have hav0 : (Multiplicative.toAdd a).val = 0 := by
      have hdvd : orderOf x ∣ (Multiplicative.toAdd a).val :=
        orderOf_dvd_of_pow_eq_one hab
      rw [hx4] at hdvd
      omega
    have ha1 : a = 1 := by
      have h0 : Multiplicative.toAdd a = 0 := (ZMod.val_eq_zero _).mp hav0
      rw [← ofAdd_toAdd a, h0, ofAdd_zero]
    have hb1 : b = 1 := by
      have h0 : Multiplicative.toAdd b = 0 := (ZMod.val_eq_zero _).mp hbv0
      rw [← ofAdd_toAdd b, h0, ofAdd_zero]
    rw [ha1, hb1]
    rfl
  have e : K8g ≃* (fx.noncommCoprod fw hcomm').range := MonoidHom.ofInjective hinj
  have hcardH : Nat.card (fx.noncommCoprod fw hcomm').range = 8 := by
    rw [← Nat.card_congr e.toEquiv]
    exact card_K8g
  have hidx : (fx.noncommCoprod fw hcomm').range.index = 2 := by
    have hmul := (fx.noncommCoprod fw hcomm').range.card_mul_index
    rw [hcardH, hcard] at hmul
    omega
  exact ⟨(fx.noncommCoprod fw hcomm').range, normal_of_index_eq_two hidx, hcardH, ⟨e.symm⟩⟩

/-- If a partition of `4` has a part `m ≥ 2`, then `partitionGroup 2 lam` has an element
whose square is nontrivial. -/
private lemma partitionGroup_sq_ne_one {a : ℕ} (lam : Nat.Partition a)
    {m : ℕ} (hm : 2 ≤ m) (hmem : m ∈ lam.parts) :
    ∃ g : partitionGroup 2 lam, g ^ 2 ≠ 1 := by
  classical
  have hmem' : m ∈ lam.parts.toList := Multiset.mem_toList.mpr hmem
  obtain ⟨j, hj_lt, hj⟩ := List.mem_iff_getElem.mp hmem'
  refine ⟨Pi.mulSingle ⟨j, hj_lt⟩
    (Multiplicative.ofAdd (1 : ZMod (2 ^ lam.parts.toList.get ⟨j, hj_lt⟩))), fun h => ?_⟩
  have hj2 := congrFun h ⟨j, hj_lt⟩
  rw [Pi.pow_apply, Pi.mulSingle_eq_same, Pi.one_apply] at hj2
  have hdvd := orderOf_dvd_of_pow_eq_one hj2
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one] at hdvd
  have hget : lam.parts.toList.get ⟨j, hj_lt⟩ = m := hj
  rw [hget] at hdvd
  have hle : 2 ^ m ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 4 ≤ 2 ^ m := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

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
    haveI : IsCyclic H := isCyclic_zpowers g
    have hH_iso : Nonempty (H ≃* C8g) :=
      cyclicRep_classification (by norm_num : (8 : ℕ) ≠ 0) hHcard
    exact Or.inl ⟨H, hHnorm, hHcard, hH_iso⟩
  · -- No element of order 8.
    -- Find an element z of order 2 in the center Z(G).
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcard_pow : Nat.card G = 2 ^ 4 := by rw [hcard]; norm_num
    have h_center_nontriv : Nontrivial (Subgroup.center G) :=
      center_nontrivial_of_card_prime_pow hcard_pow (by norm_num : (0 : ℕ) < 4)
    haveI hc_nontriv : Nontrivial (Subgroup.center G) := h_center_nontriv
    obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center G)
    have hw_ne_one : (w : G) ≠ 1 := Subtype.coe_inj.not.mpr hw
    have hcard_fin : Fintype.card G = 16 := by
      rw [Fintype.card_eq_nat_card, hcard]
    have hw_order_dvd : orderOf (w : G) ∣ 16 := by
      rw [← hcard_fin]; exact orderOf_dvd_card
    have hw_order_not8 : orderOf (w : G) ≠ 8 := by
      intro h; apply h_ord8; exact ⟨(w : G), h⟩
    -- orderOf w ∈ {1,2,4}. Not 1 (nontrivial), not 8 (by assumption).
    have hw_order_24 : orderOf (w : G) = 2 ∨ orderOf (w : G) = 4 := by
      have hpos : 0 < orderOf (w : G) := orderOf_pos _
      have h_not1 : orderOf (w : G) ≠ 1 := by
        intro h1; apply hw_ne_one; exact (orderOf_eq_one_iff.mp h1)
      have h_not16 : orderOf (w : G) ≠ 16 := by
        intro h16
        have h8 : orderOf ((w : G) ^ 2) = 8 := by
          rw [orderOf_pow (w : G), h16]
          norm_num
        apply h_ord8
        exact ⟨(w : G) ^ 2, h8⟩
      have h_all_divs : (Nat.divisors 16) = {1,2,4,8,16} := by decide
      have h_mem : orderOf (w : G) ∈ Nat.divisors 16 :=
        Nat.mem_divisors.mpr ⟨hw_order_dvd, by norm_num⟩
      rw [h_all_divs] at h_mem
      have h_cases : orderOf (w : G) = 2 ∨ orderOf (w : G) = 4 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
        rcases h_mem with (h1 | h2 | h4 | h8 | h16)
        · exact (h_not1 h1).elim
        · left; exact h2
        · right; exact h4
        · exact (hw_order_not8 h8).elim
        · exact (h_not16 h16).elim
      exact h_cases
    -- Obtain nontrivial z ∈ Z(G) with orderOf z = 2
    have h_exists_z2 : ∃ z : G, z ∈ Subgroup.center G ∧ orderOf z = 2 := by
      rcases hw_order_24 with (hw2 | hw4)
      · exact ⟨(w : G), w.property, hw2⟩
      · refine ⟨(w : G) ^ 2, Subgroup.pow_mem _ w.property 2, ?_⟩
        rw [orderOf_pow (w : G), hw4]
        norm_num
    obtain ⟨z, hz_cent, hz_order2⟩ := h_exists_z2
    have hz_ne_one : z ≠ 1 := by
      intro h; rw [h, orderOf_one] at hz_order2; omega
    -- Now z is a central element of order 2.  Continue with Wild's case analysis.
    -- By Fact 2 (all elements squared = 1 ⇒ abelian), since G ≄ (C₂)⁴, there exists
    -- an element of order 4.  Otherwise G would be abelian exponent 2, hence ≅ (C₂)⁴.
    have h_exists_ord4 : ∃ x : G, orderOf x = 4 := by
      by_contra! h_no4
      -- If no element of order 4, then every element squares to 1.
      have h_all_sq_one : ∀ g : G, g ^ 2 = 1 := by
        intro g
        have hord : orderOf g = 1 ∨ orderOf g = 2 := by
          have hpos : 0 < orderOf g := orderOf_pos _
          have h_dvd : orderOf g ∣ 16 := by
            rw [← hcard_fin]; exact orderOf_dvd_card
          have h_not8 : orderOf g ≠ 8 := by
            intro h; apply h_ord8; exact ⟨g, h⟩
          have h_not16 : orderOf g ≠ 16 := by
            intro h16
            have h8 : orderOf (g ^ 2) = 8 := by
              rw [orderOf_pow g, h16]; norm_num
            apply h_ord8; exact ⟨g ^ 2, h8⟩
          have h_not4 : orderOf g ≠ 4 := h_no4 g
          have h_mem : orderOf g ∈ Nat.divisors 16 :=
            Nat.mem_divisors.mpr ⟨h_dvd, by norm_num⟩
          have h_divs : (Nat.divisors 16) = {1,2,4,8,16} := by decide
          rw [h_divs] at h_mem
          simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
          rcases h_mem with (h1 | h2' | h4 | h8 | h16)
          · left; exact h1
          · right; exact h2'
          · exact (h_not4 h4).elim
          · exact (h_not8 h8).elim
          · exact (h_not16 h16).elim
        rcases hord with (h1 | h2')
        · have hg1 : g = 1 := orderOf_eq_one_iff.mp h1
          rw [hg1, one_pow]
        · have htemp := pow_orderOf_eq_one g
          rw [h2'] at htemp; exact htemp
      have h_abel : ∀ a b : G, a * b = b * a := mul_comm_of_sq_eq_one h_all_sq_one
      -- G is abelian of order 2⁴ and exponent 2, hence ≅ (C₂)⁴ = G₀, contradicting h_not_elem
      letI : CommGroup G := { ‹Group G› with mul_comm := h_abel }
      have hcontra : ∀ (lam : Nat.Partition 4) (m : ℕ), 2 ≤ m → m ∈ lam.parts →
          (G ≃* partitionGroup 2 lam) → False := by
        intro lam m hm hmem e
        obtain ⟨g, hg⟩ := partitionGroup_sq_ne_one lam hm hmem
        apply hg
        calc g ^ 2 = e (e.symm g) ^ 2 := by rw [MulEquiv.apply_symm_apply]
          _ = e (e.symm g ^ 2) := (map_pow e _ 2).symm
          _ = e 1 := by rw [h_all_sq_one (e.symm g)]
          _ = 1 := map_one e
      obtain ⟨i, ⟨e⟩⟩ := orderP4Abel_complete 2 G (by rw [hcard]; norm_num)
      fin_cases i
      · exact hcontra part4 4 (by norm_num) (by decide) e
      · exact hcontra part31 3 (by norm_num) (by decide) e
      · exact hcontra part22 2 (by norm_num) (by decide) e
      · exact hcontra part211 2 (by norm_num) (by decide) e
      · exact h_not_elem ⟨e⟩
    obtain ⟨x, hx_order4⟩ := h_exists_ord4
    have hz2 : z ^ 2 = 1 := by
      have htemp := pow_orderOf_eq_one z
      rw [hz_order2] at htemp; exact htemp
    have hOrders : ∀ g : G, orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 4 :=
      orderOf_cases_of_card16 hcard h_ord8
    by_cases hsq_all : ∀ u : G, orderOf u = 4 → u ^ 2 = z
    · -- Case 2 of Wild: every element of order 4 squares to z.
      -- Then G/⟨z⟩ has exponent 2, hence is abelian, so the conjugacy class of x is
      -- contained in {x, zx}; the centralizer of x has order ≥ 8 and yields an element
      -- y ∉ ⟨x⟩ commuting with x, from which we build a normal K₈.
      have hx2z : x ^ 2 = z := hsq_all x hx_order4
      have hN_norm : (Subgroup.zpowers z).Normal := by
        constructor
        intro n hn g
        have hcn : ∀ h : G, h * n = n * h :=
          Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr hz_cent) hn)
        have hfix : g * n * g⁻¹ = n := by rw [hcn g]; group
        rw [hfix]; exact hn
      haveI := hN_norm
      have hN_two : ∀ n : G, n ∈ Subgroup.zpowers z → n = 1 ∨ n = z := by
        intro n hn
        obtain ⟨m, hm_lt, hm⟩ :=
          exists_pow_eq_of_mem_zpowers (by rw [hz_order2]; norm_num) hn
        rw [hz_order2] at hm_lt
        interval_cases m
        · left; rw [← hm, pow_zero]
        · right; rw [← hm, pow_one]
      -- The quotient G/⟨z⟩ has exponent 2, hence is abelian
      have hquot_sq : ∀ q : G ⧸ Subgroup.zpowers z, q ^ 2 = 1 := by
        intro q
        refine QuotientGroup.induction_on q ?_
        intro g
        have hg2 : g * g ∈ Subgroup.zpowers z := by
          rw [← pow_two]
          rcases hOrders g with h1 | h2 | h4
          · rw [orderOf_eq_one_iff.mp h1, one_pow]; exact Subgroup.one_mem _
          · have := pow_orderOf_eq_one g
            rw [h2] at this
            rw [this]; exact Subgroup.one_mem _
          · rw [hsq_all g h4]; exact Subgroup.mem_zpowers z
        rw [pow_two, ← QuotientGroup.mk_mul]
        exact (QuotientGroup.eq_one_iff _).mpr hg2
      have hquot_comm : ∀ a b : G ⧸ Subgroup.zpowers z, a * b = b * a :=
        mul_comm_of_sq_eq_one hquot_sq
      -- Every conjugate of x lies in the coset {x, zx}
      have hconj_mem : ∀ g : G, g * x * g⁻¹ * x⁻¹ ∈ Subgroup.zpowers z := by
        intro g
        rw [← QuotientGroup.eq_one_iff]
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv, QuotientGroup.mk_inv]
        rw [hquot_comm (g : G ⧸ Subgroup.zpowers z) (x : G ⧸ Subgroup.zpowers z)]
        group
      have hconj_cases : ∀ g : G, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = z * x := by
        intro g
        rcases hN_two _ (hconj_mem g) with h1 | h1
        · left
          have h2 : g * x * g⁻¹ * x⁻¹ * x = 1 * x := by rw [h1]
          simpa using h2
        · right
          have h2 : g * x * g⁻¹ * x⁻¹ * x = z * x := by rw [h1]
          simpa using h2
      -- Orbit–stabilizer: the centralizer of x has at least 8 elements
      have horb_le : Nat.card (MulAction.orbit (ConjAct G) x) ≤ 2 := by
        have hsub : MulAction.orbit (ConjAct G) x ⊆ ({x, z * x} : Set G) := by
          rintro u ⟨h, rfl⟩
          simp only [ConjAct.smul_def, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact hconj_cases (ConjAct.ofConjAct h)
        calc Nat.card (MulAction.orbit (ConjAct G) x)
            = (MulAction.orbit (ConjAct G) x).ncard := Nat.card_coe_set_eq _
          _ ≤ ({x, z * x} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ ({z * x} : Set G).ncard + 1 := Set.ncard_insert_le _ _
          _ = 2 := by rw [Set.ncard_singleton]
      have hcardS : 8 ≤ Nat.card (MulAction.stabilizer (ConjAct G) x) := by
        have hprod := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct G) x)
        have hcardCG : Nat.card (ConjAct G) = 16 := by
          rw [← hcard]
          exact Nat.card_congr ConjAct.ofConjAct.toEquiv
        rw [hcardCG] at hprod
        have hidx_le : (MulAction.stabilizer (ConjAct G) x).index ≤ 2 := by
          have hindex_eq : (MulAction.stabilizer (ConjAct G) x).index
              = Nat.card (MulAction.orbit (ConjAct G) x) := by
            rw [Subgroup.index_eq_card]
            exact (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) x)).symm
          rw [hindex_eq]
          exact horb_le
        have h012 : (MulAction.stabilizer (ConjAct G) x).index = 0 ∨
            (MulAction.stabilizer (ConjAct G) x).index = 1 ∨
            (MulAction.stabilizer (ConjAct G) x).index = 2 := by omega
        rcases h012 with h | h | h <;> rw [h] at hprod <;> omega
      -- The powers of x form a subgroup of order 4 inside the stabilizer
      have hT_le : Subgroup.zpowers (ConjAct.toConjAct x) ≤
          MulAction.stabilizer (ConjAct G) x := by
        rw [Subgroup.zpowers_le]
        rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
        group
      have hcardT : Nat.card (Subgroup.zpowers (ConjAct.toConjAct x)) = 4 := by
        rw [Nat.card_zpowers,
          show ConjAct.toConjAct x = ConjAct.toConjAct.toMonoidHom x from rfl,
          orderOf_injective ConjAct.toConjAct.toMonoidHom ConjAct.toConjAct.injective,
          hx_order4]
      have hnotle : ¬ (MulAction.stabilizer (ConjAct G) x ≤
          Subgroup.zpowers (ConjAct.toConjAct x)) := by
        intro hle
        have hle_card := Subgroup.card_le_of_le hle
        omega
      obtain ⟨hc, hhS, hhT⟩ := SetLike.not_le_iff_exists.mp hnotle
      -- y := ofConjAct hc commutes with x and lies outside ⟨x⟩
      have hyx : ConjAct.ofConjAct hc * x * (ConjAct.ofConjAct hc)⁻¹ = x := by
        have hs := MulAction.mem_stabilizer_iff.mp hhS
        rwa [ConjAct.smul_def] at hs
      have hxy_comm : Commute x (ConjAct.ofConjAct hc) := by
        have h1 : ConjAct.ofConjAct hc * x = x * ConjAct.ofConjAct hc := by
          calc ConjAct.ofConjAct hc * x
              = (ConjAct.ofConjAct hc * x * (ConjAct.ofConjAct hc)⁻¹) *
                ConjAct.ofConjAct hc := by group
            _ = x * ConjAct.ofConjAct hc := by rw [hyx]
        exact h1.symm
      have hy_notin : ConjAct.ofConjAct hc ∉ Subgroup.zpowers x := by
        intro hmem
        apply hhT
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hk' : (ConjAct.toConjAct x) ^ k = hc := by
          rw [show ConjAct.toConjAct x = ConjAct.toConjAct.toMonoidHom x from rfl,
            ← map_zpow, hk]
          exact ConjAct.toConjAct_ofConjAct hc
        rw [← hk']
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
      rcases hOrders (ConjAct.ofConjAct hc) with hy1 | hy2 | hy4
      · exfalso
        apply hy_notin
        rw [orderOf_eq_one_iff.mp hy1]
        exact Subgroup.one_mem _
      · -- y has order 2: ⟨x, y⟩ is a normal K₈
        obtain ⟨H, hH1, hH2, hH3⟩ := normal_k8_of_commuting hcard x
          (ConjAct.ofConjAct hc) hx_order4 hy2 hxy_comm hy_notin
        exact Or.inr ⟨H, hH1, hH2, hH3⟩
      · -- y has order 4: then y² = z, so xy has order 2 and ⟨x, xy⟩ is a normal K₈
        have hy2z : (ConjAct.ofConjAct hc) ^ 2 = z := hsq_all _ hy4
        have hxy_sq : (x * ConjAct.ofConjAct hc) ^ 2 = 1 := by
          have hstep : (x * ConjAct.ofConjAct hc) ^ 2 =
              x ^ 2 * (ConjAct.ofConjAct hc) ^ 2 := by
            calc (x * ConjAct.ofConjAct hc) ^ 2
                = x * (ConjAct.ofConjAct hc * x) * ConjAct.ofConjAct hc := by
                  rw [pow_two]; group
              _ = x * (x * ConjAct.ofConjAct hc) * ConjAct.ofConjAct hc := by
                  rw [← hxy_comm.eq]
              _ = x ^ 2 * (ConjAct.ofConjAct hc) ^ 2 := by
                  rw [pow_two, pow_two]; group
          rw [hstep, hx2z, hy2z, ← pow_two, hz2]
        have hxy_ne : x * ConjAct.ofConjAct hc ≠ 1 := by
          intro h1
          apply hy_notin
          have h2 : ConjAct.ofConjAct hc = x⁻¹ := eq_inv_of_mul_eq_one_right h1
          rw [h2]
          exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
        have hxy_ord : orderOf (x * ConjAct.ofConjAct hc) = 2 :=
          orderOf_eq_prime hxy_sq hxy_ne
        have hxy_comm' : Commute x (x * ConjAct.ofConjAct hc) :=
          (Commute.refl x).mul_right hxy_comm
        have hxy_notin : x * ConjAct.ofConjAct hc ∉ Subgroup.zpowers x := by
          intro hmem
          apply hy_notin
          have h2 : ConjAct.ofConjAct hc = x⁻¹ * (x * ConjAct.ofConjAct hc) := by group
          rw [h2]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) hmem
        obtain ⟨H, hH1, hH2, hH3⟩ := normal_k8_of_commuting hcard x
          (x * ConjAct.ofConjAct hc) hx_order4 hxy_ord hxy_comm' hxy_notin
        exact Or.inr ⟨H, hH1, hH2, hH3⟩
    · -- Case 1 of Wild: some element u of order 4 has u² ≠ z; then ⟨u, z⟩ ≅ K₈
      push Not at hsq_all
      obtain ⟨u, hu4, husq⟩ := hsq_all
      have hu_comm : Commute u z := Subgroup.mem_center_iff.mp hz_cent u
      have hz_notin : z ∉ Subgroup.zpowers u := by
        intro hmem
        obtain ⟨m, hm_lt, hm⟩ :=
          exists_pow_eq_of_mem_zpowers (by rw [hu4]; norm_num) hmem
        rw [hu4] at hm_lt
        interval_cases m
        · rw [pow_zero] at hm; exact hz_ne_one hm.symm
        · rw [pow_one] at hm
          rw [hm] at hu4
          omega
        · exact husq hm
        · have hord3 : orderOf (u ^ 3) = 4 := by
            rw [orderOf_pow u, hu4]
            norm_num
          rw [hm, hz_order2] at hord3
          omega
      obtain ⟨H, hH1, hH2, hH3⟩ :=
        normal_k8_of_commuting hcard u z hu4 hz_order2 hu_comm hz_notin
      exact Or.inr ⟨H, hH1, hH2, hH3⟩

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
