/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Polycyclic groups, layer by layer: cyclic extensions

The first ingredient of the polycyclic (pc) group machinery: a **cyclic extension**
of a group `G` by `C_r` is determined by the data `(f, a, r)` where

* `f : G → G` is (the function underlying) the conjugation action of the new
  generator `t` — an automorphism of `G` when the data is consistent,
* `a : G` is the power element `t ^ r`,

subject to the consistency conditions `CycExtData.Consistent`:
`f` is multiplicative, bijective, fixes `a`, and `f^[r]` is conjugation by `a`.

The extension `CycExt D` has carrier `G × ZMod r`, the pair `(g, i)` representing the
normal form `g * t ⁱ`, with multiplication

  `(g, i) * (h, j) = (g * f^[i.val] h * (if i.val + j.val < r then 1 else a), i + j)`.

The data is kept **proof-free** (`f` is a bare function, not a `MulAut`) so that
towers of extensions can be built computably from raw pc presentations; the `Group`
instance and the extension-theoretic interface are available once consistency is
registered (`instance : D.Consistent := by decide` for concrete data):

* `CycExt.inl : G →* CycExt D` embeds `G`, its range is the kernel of the
  projection and hence normal (`CycExt.ker_rightHom`);
* `CycExt.rightHom : CycExt D →* Multiplicative (ZMod r)` is the projection;
* `CycExt.card_cycExt` — the extension has order `r * |G|`;
* `CycExt.gen` is the new generator `t = (1, 1)`, satisfying `gen ^ r = inl a`
  (`CycExt.gen_pow`) and `gen * inl g * gen⁻¹ = inl (f g)`
  (`CycExt.gen_mul_inl_mul_gen_inv`); every element factors as
  `x = inl x.fst * gen ^ x.snd.val` (`CycExt.eq_inl_mul_gen_pow`).

Iterating this construction from the trivial group builds every polycyclic group
from its pc presentation; see `Polycyclic/Basic.lean`.  The construction mirrors
`PGroupGeneration/CocycleGroup.lean` (which is the special case `f = id`,
i.e. central extensions).
-/

namespace Smallgroups.GAP

/-- The raw data of a **cyclic extension** of `G` by `C_r`: a function `f` (the
conjugation action of the new generator `t`) and the power element `a = t ^ r`.
The consistency conditions are separate (`CycExtData.Consistent`), so that the data
is proof-free and towers of extensions can be computed from raw pc presentations. -/
structure CycExtData (G : Type*) where
  /-- The relative order of the new generator. -/
  r : ℕ
  /-- The conjugation action of the new generator. -/
  f : G → G
  /-- The power element `t ^ r`. -/
  a : G
  /-- The relative order is positive. -/
  hr : 0 < r

namespace CycExtData

variable {G : Type*} (D : CycExtData G)

instance : NeZero D.r := ⟨Nat.pos_iff_ne_zero.mp D.hr⟩

/-- The consistency conditions for cyclic extension data: `f` is multiplicative,
bijective, fixes the power element `a`, and `f^[r]` is conjugation by `a`.  For
concrete data over a finite `G` this is decidable (`by decide`). -/
class Consistent {G : Type*} [Mul G] [One G] [Inv G] (D : CycExtData G) : Prop where
  /-- `f` is multiplicative. -/
  hom : ∀ x y, D.f (x * y) = D.f x * D.f y
  /-- `f` fixes `1`. -/
  one : D.f 1 = 1
  /-- `f` is bijective. -/
  bij : Function.Bijective D.f
  /-- `f` fixes the power element. -/
  fixa : D.f D.a = D.a
  /-- `f^[r]` is conjugation by `a`. -/
  powconj : ∀ x, D.f^[D.r] x = D.a * x * D.a⁻¹

/-- Consistency is decidable over finite types. -/
instance decidableConsistent {G : Type*} [Mul G] [One G] [Inv G] [Fintype G]
    [DecidableEq G] (D : CycExtData G) : Decidable D.Consistent :=
  decidable_of_iff' _
    (show D.Consistent ↔ (∀ x y, D.f (x * y) = D.f x * D.f y) ∧ D.f 1 = 1 ∧
        Function.Bijective D.f ∧ D.f D.a = D.a ∧ ∀ x, D.f^[D.r] x = D.a * x * D.a⁻¹ from
      ⟨fun h => ⟨h.hom, h.one, h.bij, h.fixa, h.powconj⟩,
        fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩)

/-- The 2-cocycle of the cyclic extension: `coc i j = a` iff the addition of the
exponents wraps around modulo `r`. -/
def coc [One G] (i j : ZMod D.r) : G :=
  if i.val + j.val < D.r then 1 else D.a

/-- The exponent form of the cocycle identity, as an equality of natural numbers. -/
theorem coc_expo_add (i j k : ZMod D.r) :
    (if i.val + j.val < D.r then 0 else 1) + (if (i + j).val + k.val < D.r then 0 else 1) =
      (if j.val + k.val < D.r then 0 else 1) +
        (if i.val + (j + k).val < D.r then 0 else 1) := by
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  have hk := ZMod.val_lt k
  rcases lt_or_ge (i.val + j.val) D.r with h1 | h1
  · rw [ZMod.val_add_of_lt h1]
    rcases lt_or_ge (j.val + k.val) D.r with h2 | h2
    · rw [ZMod.val_add_of_lt h2]
      split_ifs with h3 h4 h5 h6 <;> omega
    · rw [ZMod.val_add_of_le h2]
      split_ifs with h3 h4 h5 h6 <;> omega
  · rw [ZMod.val_add_of_le h1]
    rcases lt_or_ge (j.val + k.val) D.r with h2 | h2
    · rw [ZMod.val_add_of_lt h2]
      split_ifs with h3 h4 h5 h6 <;> omega
    · rw [ZMod.val_add_of_le h2]
      split_ifs with h3 h4 h5 h6 <;> omega

variable [Group G] {D}

namespace Consistent

variable (h : D.Consistent)

include h

/-- All iterates of `f` fix `1`. -/
theorem iterate_one (n : ℕ) : D.f^[n] 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, h.one, ih]

/-- All iterates of `f` are multiplicative. -/
theorem iterate_mul (n : ℕ) (x y : G) : D.f^[n] (x * y) = D.f^[n] x * D.f^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih]; exact h.hom _ _

/-- `f` commutes with inversion. -/
theorem inv (x : G) : D.f x⁻¹ = (D.f x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← h.hom, inv_mul_cancel, h.one])

/-- All iterates of `f` commute with inversion. -/
theorem iterate_inv (n : ℕ) (x : G) : D.f^[n] x⁻¹ = (D.f^[n] x)⁻¹ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, h.inv, Function.iterate_succ_apply']

/-- All iterates of `f` fix the power element. -/
theorem iterate_a (n : ℕ) : D.f^[n] D.a = D.a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, h.fixa]

/-- All iterates of `f` commute with powers. -/
theorem iterate_pow (n : ℕ) (x : G) (k : ℕ) : D.f^[n] (x ^ k) = (D.f^[n] x) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, h.iterate_one]
  | succ k ih => rw [pow_succ, h.iterate_mul, ih, pow_succ]

end Consistent

/-- The cocycle takes values in `{1, a}`. -/
theorem coc_eq_pow (i j : ZMod D.r) :
    D.coc i j = D.a ^ (if i.val + j.val < D.r then 0 else 1) := by
  by_cases h : i.val + j.val < D.r <;> simp [coc, h]

/-- All iterates of `f` fix the cocycle values. -/
theorem Consistent.iterate_coc (h : D.Consistent) (n : ℕ) (i j : ZMod D.r) :
    D.f^[n] (D.coc i j) = D.coc i j := by
  rw [coc_eq_pow, h.iterate_pow, h.iterate_a]

/-- Cocycle values commute with each other. -/
theorem coc_comm (i j k l : ZMod D.r) :
    D.coc i j * D.coc k l = D.coc k l * D.coc i j := by
  rw [coc_eq_pow, coc_eq_pow, ← pow_add, ← pow_add, Nat.add_comm]

/-- The cocycle identity. -/
theorem coc_mul (i j k : ZMod D.r) :
    D.coc i j * D.coc (i + j) k = D.coc j k * D.coc i (j + k) := by
  rw [coc_eq_pow, coc_eq_pow, coc_eq_pow, coc_eq_pow, ← pow_add, ← pow_add, coc_expo_add]

/-- Key lemma: `f^[i.val + j.val]` is `f^[(i + j).val]` conjugated by the cocycle. -/
theorem Consistent.iterate_add_val (h : D.Consistent) (i j : ZMod D.r) (g : G) :
    D.f^[i.val + j.val] g = D.coc i j * D.f^[(i + j).val] g * (D.coc i j)⁻¹ := by
  by_cases hc : i.val + j.val < D.r
  · rw [ZMod.val_add_of_lt hc]
    simp [coc, hc]
  · have v : (i + j).val = i.val + j.val - D.r := ZMod.val_add_of_le (le_of_not_gt hc)
    have e : i.val + j.val = (i.val + j.val - D.r) + D.r :=
      (Nat.sub_add_cancel (le_of_not_gt hc)).symm
    rw [e, Function.iterate_add_apply, h.powconj, v]
    simp only [coc, if_neg hc, h.iterate_mul, h.iterate_inv, h.iterate_a, mul_assoc]

end CycExtData

/-- A generic rearrangement identity used in the associativity proof. -/
theorem mul_rearrange {G : Type*} [Group G] {u v w c₁ c₂ c₃ c₄ : G} (h : c₂ * c₃ = c₁ * c₄) :
    u * v * c₁ * w * c₄ = u * (v * (c₁ * w * c₁⁻¹) * c₂) * c₃ := by
  have e : c₄ = c₁⁻¹ * c₂ * c₃ := by
    rw [mul_assoc, h, inv_mul_cancel_left]
  rw [e]
  group

/-- The cyclic extension of `G` by `C_r` determined by `D`: the carrier is
`G × ZMod D.r`, with `(g, i)` representing the normal form `g * t ⁱ`. -/
@[ext]
structure CycExt {G : Type*} (D : CycExtData G) where
  /-- The `G`-component. -/
  fst : G
  /-- The exponent component. -/
  snd : ZMod D.r

namespace CycExt

variable {G : Type*} (D : CycExtData G)

instance instMul [Mul G] [One G] : Mul (CycExt D) :=
  ⟨fun x y => ⟨x.fst * D.f^[x.snd.val] y.fst * D.coc x.snd y.snd, x.snd + y.snd⟩⟩

instance instOne [One G] : One (CycExt D) := ⟨⟨1, 0⟩⟩

instance instInv [Mul G] [One G] [Inv G] : Inv (CycExt D) :=
  ⟨fun x => ⟨D.f^[(-x.snd).val] ((D.coc x.snd (-x.snd))⁻¹ * x.fst⁻¹), -x.snd⟩⟩

@[simp] theorem mul_fst [Mul G] [One G] (x y : CycExt D) :
    (x * y).fst = x.fst * D.f^[x.snd.val] y.fst * D.coc x.snd y.snd := rfl

@[simp] theorem mul_snd [Mul G] [One G] (x y : CycExt D) :
    (x * y).snd = x.snd + y.snd := rfl

@[simp] theorem one_fst [One G] : (1 : CycExt D).fst = 1 := rfl

@[simp] theorem one_snd [One G] : (1 : CycExt D).snd = 0 := rfl

@[simp] theorem inv_fst [Mul G] [One G] [Inv G] (x : CycExt D) :
    x⁻¹.fst = D.f^[(-x.snd).val] ((D.coc x.snd (-x.snd))⁻¹ * x.fst⁻¹) := rfl

@[simp] theorem inv_snd [Mul G] [One G] [Inv G] (x : CycExt D) : x⁻¹.snd = -x.snd := rfl

@[simp] theorem coc_zero_left [One G] (j : ZMod D.r) : D.coc 0 j = 1 := by
  unfold CycExtData.coc
  rw [if_pos (by simpa using ZMod.val_lt j)]

@[simp] theorem coc_zero_right [One G] (i : ZMod D.r) : D.coc i 0 = 1 := by
  unfold CycExtData.coc
  rw [if_pos (by simpa using ZMod.val_lt i)]

@[simp] theorem coc_neg_self [Group G] (i : ZMod D.r) :
    D.coc i (-i) = D.coc (-i) i := by
  rw [CycExtData.coc_eq_pow, CycExtData.coc_eq_pow, Nat.add_comm]

/-- The group structure on the cyclic extension, from consistent data. -/
instance group [Group G] [h : D.Consistent] : Group (CycExt D) where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc x y z := by
    ext
    · simp only [mul_fst, mul_snd, h.iterate_mul, h.iterate_coc,
        ← Function.iterate_add_apply]
      rw [h.iterate_add_val x.snd y.snd z.fst]
      exact mul_rearrange (CycExtData.coc_mul x.snd y.snd z.snd).symm
    · simp only [mul_snd, add_assoc]
  one_mul x := by
    ext
    · simp only [mul_fst, one_fst, one_snd, ZMod.val_zero, Function.iterate_zero_apply,
        coc_zero_left, one_mul, mul_one]
    · simp
  mul_one x := by
    ext
    · simp only [mul_fst, one_fst, one_snd, h.iterate_one, coc_zero_right, mul_one]
    · simp
  inv_mul_cancel x := by
    ext
    · simp only [mul_fst, inv_fst, inv_snd, one_fst, h.iterate_mul, h.iterate_inv,
        h.iterate_coc, coc_neg_self]
      group
    · simp

/-- The raw embedding function `G → CycExt D`, `g ↦ (g, 0)`. -/
def inlFn : G → CycExt D := fun g => ⟨g, 0⟩

@[simp] theorem inlFn_fst (g : G) : (inlFn D g).fst = g := rfl

@[simp] theorem inlFn_snd (g : G) : (inlFn D g).snd = 0 := rfl

/-- The embedding `G → CycExt D` as a homomorphism; its image is a normal subgroup. -/
def inl [Group G] [D.Consistent] : G →* CycExt D where
  toFun := inlFn D
  map_one' := by ext <;> simp [inlFn]
  map_mul' g h := by
    ext
    · simp [inlFn, Function.iterate_zero_apply]
    · simp [inlFn]

@[simp] theorem inl_fst [Group G] [D.Consistent] (g : G) : (inl D g).fst = g := rfl

@[simp] theorem inl_snd [Group G] [D.Consistent] (g : G) : (inl D g).snd = 0 := rfl

theorem inl_injective [Group G] [D.Consistent] : Function.Injective (inl D) := by
  intro g h e
  have h2 := congrArg CycExt.fst e
  simpa using h2

/-- The projection to the exponent, `CycExt D →* Multiplicative (ZMod D.r)`. -/
def rightHom [Group G] [D.Consistent] : CycExt D →* Multiplicative (ZMod D.r) where
  toFun x := Multiplicative.ofAdd x.snd
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem rightHom_apply [Group G] [D.Consistent] (x : CycExt D) :
    rightHom D x = Multiplicative.ofAdd x.snd := rfl

theorem rightHom_surjective [Group G] [D.Consistent] : Function.Surjective (rightHom D) :=
  fun m => ⟨⟨1, m.toAdd⟩, rfl⟩

@[simp] theorem rightHom_inl [Group G] [D.Consistent] (g : G) :
    rightHom D (inl D g) = 1 := rfl

/-- The kernel of the projection is exactly the embedded copy of `G`. -/
theorem ker_rightHom [Group G] [D.Consistent] :
    (rightHom D).ker = (inl D).range := by
  ext x
  constructor
  · intro hx
    have hx' : x.snd = 0 := Multiplicative.ofAdd.injective hx
    exact ⟨x.fst, by ext <;> simp [hx']⟩
  · rintro ⟨g, rfl⟩
    rfl

/-- The embedded copy of `G` is a normal subgroup (it is a kernel). -/
instance [Group G] [D.Consistent] : (inl D).range.Normal := by
  rw [← ker_rightHom D]
  infer_instance

/-- `CycExt D` is in (set-theoretic) bijection with `G × ZMod D.r`. -/
def toProd : CycExt D ≃ G × ZMod D.r where
  toFun x := (x.fst, x.snd)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instDecidableEq [DecidableEq G] : DecidableEq (CycExt D) :=
  fun _ _ => decidable_of_iff' _ CycExt.ext_iff

instance instFintype [Fintype G] [DecidableEq G] : Fintype (CycExt D) :=
  Fintype.ofEquiv _ (toProd D).symm

/-- The extension has order `r * |G|`. -/
theorem card_cycExt [Finite G] : Nat.card (CycExt D) = D.r * Nat.card G := by
  have hz : Nat.card (ZMod D.r) = D.r := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [Nat.card_congr (toProd D), Nat.card_prod, hz, mul_comm]

/-- The quotient of the extension by the embedded copy of `G` recovers `C_r`. -/
noncomputable def quotientRangeInlEquiv [Group G] [D.Consistent] :
    (CycExt D ⧸ (inl D).range) ≃* Multiplicative (ZMod D.r) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_rightHom D).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (rightHom_surjective D))

/-- The new generator `t = (1, 1)`. -/
def gen [One G] : CycExt D := ⟨1, 1⟩

@[simp] theorem gen_fst [One G] : (gen D).fst = 1 := rfl

@[simp] theorem gen_snd [One G] : (gen D).snd = 1 := rfl

/-- Small powers of the new generator: `t ⁿ = (1, n)` for `n < r`. -/
theorem gen_pow_lt [Group G] [h : D.Consistent] {n : ℕ} (hn : n < D.r) :
    (gen D) ^ n = ⟨1, (n : ZMod D.r)⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
      have hn' : n < D.r := Nat.lt_of_succ_lt hn
      rw [pow_succ, ih hn']
      ext
      · simp only [mul_fst, gen_fst, gen_snd, h.iterate_one, one_mul, mul_one]
        unfold CycExtData.coc
        have hval : (1 : ZMod D.r).val = 1 := by
          haveI : Fact (1 < D.r) := ⟨by omega⟩
          exact ZMod.val_one _
        rw [if_pos (by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn', hval]; exact hn)]
      · simp [mul_snd, gen_snd]

/-- Factorization: `x = inl x.fst * t ^ (x.snd.val)`. -/
theorem eq_inl_mul_gen_pow [Group G] [h : D.Consistent] (x : CycExt D) :
    x = inl D x.fst * (gen D) ^ x.snd.val := by
  rw [gen_pow_lt D (ZMod.val_lt x.snd)]
  ext
  · simp only [mul_fst, inl_fst, inl_snd, ZMod.val_zero, Function.iterate_zero_apply,
      mul_one, coc_zero_left]
  · simp [mul_snd, inl_snd]

/-- The defining power relation: `t ^ r = inl a`. -/
theorem gen_pow [Group G] [h : D.Consistent] (hr2 : 2 ≤ D.r) :
    (gen D) ^ D.r = inl D D.a := by
  haveI : Fact (1 < D.r) := ⟨hr2⟩
  have h1r : 1 ≤ D.r := Nat.succ_le_of_lt D.hr
  rw [show D.r = D.r - 1 + 1 from (Nat.sub_add_cancel h1r).symm, pow_succ,
    gen_pow_lt D (by have := D.hr; omega)]
  ext
  · simp only [mul_fst, gen_fst, gen_snd, h.iterate_one, one_mul, inl_fst]
    unfold CycExtData.coc
    rw [if_neg (by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := D.hr; omega), ZMod.val_one D.r]
      have := D.hr; omega)]
  · simp only [mul_snd, gen_snd, inl_snd]
    rw [show (1 : ZMod D.r) = ((1 : ℕ) : ZMod D.r) from (Nat.cast_one).symm,
      ← Nat.cast_add, Nat.sub_add_cancel h1r, ZMod.natCast_self]

/-- The defining conjugation relation: `t * inl g * t⁻¹ = inl (f g)`. -/
theorem gen_mul_inl_mul_gen_inv [Group G] [h : D.Consistent] (hr2 : 2 ≤ D.r) (g : G) :
    gen D * inl D g * (gen D)⁻¹ = inl D (D.f g) := by
  haveI : Fact (1 < D.r) := ⟨hr2⟩
  have h1val : (1 : ZMod D.r).val = 1 := ZMod.val_one _
  have hnegval : (-1 : ZMod D.r).val = D.r - 1 := by
    have h1 : ((1 : ZMod D.r) + (-1)).val = 0 := by
      rw [add_neg_cancel]; exact ZMod.val_zero
    rcases lt_or_ge ((1 : ZMod D.r).val + (-1 : ZMod D.r).val) D.r with hc | hc
    · rw [ZMod.val_add_of_lt hc, h1val] at h1
      omega
    · rw [ZMod.val_add_of_le hc, h1val] at h1
      have h2 := ZMod.val_lt (-1 : ZMod D.r)
      have h3 := D.hr
      omega
  have hcoc : D.coc 1 (-1) = D.a := by
    unfold CycExtData.coc
    rw [if_neg (by rw [h1val, hnegval]; have := D.hr; omega)]
  have step : gen D * inl D g = ⟨D.f g, 1⟩ := by
    ext
    · simp only [mul_fst, gen_fst, gen_snd, inl_fst, inl_snd, one_mul, coc_zero_right,
        mul_one, h1val, Function.iterate_one]
    · simp [mul_snd, gen_snd, inl_snd]
  rw [step]
  ext
  · simp only [mul_fst, inv_fst, inv_snd, gen_fst, gen_snd, inl_fst, h1val,
      hnegval, inv_one, mul_one, hcoc, h.iterate_inv, h.iterate_a, inv_mul_cancel_right]
  · simp [mul_snd, inv_snd, gen_snd, inl_snd]

/-- Two homomorphisms out of `CycExt D` are equal once they agree on the embedded
copy of `G` and on the new generator. -/
theorem hom_ext [Group G] [D.Consistent] {H : Type*} [Group H] {φ ψ : CycExt D →* H}
    (h1 : ∀ x, φ (inl D x) = ψ (inl D x)) (h2 : φ (gen D) = ψ (gen D)) : φ = ψ := by
  ext x
  rw [eq_inl_mul_gen_pow D x, map_mul, map_mul, map_pow, map_pow, h1, h2]

end CycExt

end Smallgroups.GAP
