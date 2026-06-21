/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order2PSqExhaustive

/-!
# Exhaustiveness for order `2 p²`: the elementary-abelian Sylow case

When the abelian Sylow-`p` subgroup is `(ℤ/p)²`, the involution `τ ∈ Aut (ℤ/p)²` splits the group
into its `+1`-eigenspace `Fix` (where `τ` acts trivially) and its `−1`-eigenspace `Neg` (where `τ`
acts by inversion).  Writing `N ≅ Fix × Neg`, the action is trivial on `Fix`, so

`G ≅ N ⋊[τ] ℤ/2 ≅ Fix × (Neg ⋊[inv] ℤ/2)`,

and the three possibilities `|Neg| ∈ {1, p, p²}` give the three representatives `R2`, `R4`, `R5`.

This file first develops the **reusable block-split lemma**: a semidirect product of a direct
product `A × B` by an action that is trivial on `A` splits off the `A` factor.
-/

namespace Smallgroups.UsefulTheorems

open SemidirectProduct

variable {A B H : Type*} [Group A] [Group B] [Group H]

/-- The block-diagonal action of `H` on `A × B` that is trivial on the first factor and acts on the
second through `ψ`. -/
def prodTrivialAction (ψ : H →* MulAut B) : H →* MulAut (A × B) where
  toFun h := MulEquiv.prodCongr (MulEquiv.refl A) (ψ h)
  map_one' := by
    apply MulEquiv.ext; intro x
    rw [map_one]
    exact Prod.ext rfl rfl
  map_mul' h h' := by
    apply MulEquiv.ext; intro x
    rw [map_mul, MulAut.mul_apply]
    exact Prod.ext rfl rfl

@[simp] theorem prodTrivialAction_apply (ψ : H →* MulAut B) (h : H) (x : A × B) :
    prodTrivialAction ψ h x = (x.1, ψ h x.2) := rfl

/-- **Block split.** A semidirect product of `A × B` by an action trivial on `A` is the direct
product of `A` with the semidirect product of `B`. -/
def semidirectProdSplit (ψ : H →* MulAut B) :
    SemidirectProduct (A × B) H (prodTrivialAction ψ) ≃* A × SemidirectProduct B H ψ where
  toFun x := (x.left.1, ⟨x.left.2, x.right⟩)
  invFun y := ⟨(y.1, y.2.left), y.2.right⟩
  left_inv x := by cases x; rfl
  right_inv y := by obtain ⟨a, b, h⟩ := y; rfl
  map_mul' x y := by
    refine Prod.ext rfl (SemidirectProduct.ext ?_ ?_) <;> rfl

/-! ### Eigenspace decomposition of an involution on an exponent-`p` abelian group

For an automorphism `τ` of a commutative group `N` with `τ² = id` and every element of order
dividing an odd `p`, the group splits as the internal direct product of the `+1`-eigenspace
`fixSubgroup` (where `τ` acts trivially) and the `−1`-eigenspace `negSubgroup` (where `τ` inverts).
The projections are `x ↦ (x · τx)^t` and `x ↦ (x · (τx)⁻¹)^t`, where `2t = p + 1`. -/

section EigenDecomp

variable {N : Type*} [CommGroup N] {τ : MulAut N} {p t : ℕ}

/-- The `+1`-eigenspace `{x | τ x = x}` of `τ`. -/
def fixSubgroup (τ : MulAut N) : Subgroup N where
  carrier := {x | τ x = x}
  one_mem' := map_one τ
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *; rw [map_mul, ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *; rw [map_inv, ha]

/-- The `−1`-eigenspace `{x | τ x = x⁻¹}` of `τ`. -/
def negSubgroup (τ : MulAut N) : Subgroup N where
  carrier := {x | τ x = x⁻¹}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *; rw [map_mul, ha, hb, mul_inv]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *; rw [map_inv, ha, inv_inv]

@[simp] lemma mem_fixSubgroup {x : N} : x ∈ fixSubgroup τ ↔ τ x = x := Iff.rfl
@[simp] lemma mem_negSubgroup {x : N} : x ∈ negSubgroup τ ↔ τ x = x⁻¹ := Iff.rfl

variable (hinv : ∀ x, τ (τ x) = x)

include hinv

lemma fixpart_mem (x : N) : (x * τ x) ^ t ∈ fixSubgroup τ := by
  rw [mem_fixSubgroup, map_pow, map_mul, hinv, mul_comm]

lemma negpart_mem (x : N) : (x * (τ x)⁻¹) ^ t ∈ negSubgroup τ := by
  rw [mem_negSubgroup, map_pow, map_mul, map_inv, hinv, ← inv_pow]
  congr 1
  rw [mul_inv, inv_inv, mul_comm]

variable (hexp : ∀ x : N, x ^ p = 1) (ht : 2 * t = p + 1)

omit hinv in
private lemma sqrt_pow_t (hexp : ∀ x : N, x ^ p = 1) (ht : 2 * t = p + 1) (x : N) :
    (x ^ 2) ^ t = x := by
  rw [← pow_mul, ht, pow_succ, hexp x, one_mul]

include hexp ht

/-- **Eigenspace decomposition.** `N ≅ fixSubgroup τ × negSubgroup τ`. -/
def eigenEquiv : N ≃* (fixSubgroup τ) × (negSubgroup τ) where
  toFun x := (⟨(x * τ x) ^ t, fixpart_mem hinv x⟩, ⟨(x * (τ x)⁻¹) ^ t, negpart_mem hinv x⟩)
  invFun y := (y.1 : N) * (y.2 : N)
  left_inv x := by
    change ((x * τ x) ^ t) * ((x * (τ x)⁻¹) ^ t) = x
    rw [← mul_pow, show (x * τ x) * (x * (τ x)⁻¹) = x ^ 2 from by
      rw [sq, mul_mul_mul_comm, mul_inv_cancel, mul_one], sqrt_pow_t hexp ht]
  right_inv y := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := y
    rw [mem_fixSubgroup] at ha
    rw [mem_negSubgroup] at hb
    apply Prod.ext
    · apply Subtype.ext
      change ((a * b) * τ (a * b)) ^ t = a
      rw [map_mul, ha, hb, show (a * b) * (a * b⁻¹) = a ^ 2 from by
        rw [sq, mul_mul_mul_comm, mul_inv_cancel, mul_one], sqrt_pow_t hexp ht]
    · apply Subtype.ext
      change ((a * b) * (τ (a * b))⁻¹) ^ t = b
      rw [map_mul, ha, hb, show (a * b) * (a * b⁻¹)⁻¹ = b ^ 2 from by
        rw [mul_inv, inv_inv, sq, mul_mul_mul_comm, mul_inv_cancel, one_mul], sqrt_pow_t hexp ht]
  map_mul' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change ((x * y) * τ (x * y)) ^ t = (x * τ x) ^ t * (y * τ y) ^ t
      rw [← mul_pow, map_mul, mul_mul_mul_comm]
    · apply Subtype.ext
      change ((x * y) * (τ (x * y))⁻¹) ^ t = (x * (τ x)⁻¹) ^ t * (y * (τ y)⁻¹) ^ t
      rw [← mul_pow, map_mul, mul_inv, mul_mul_mul_comm]

/-- Under the eigenspace decomposition, `τ` acts as the identity on `fixSubgroup` and by inversion
on `negSubgroup`. -/
lemma eigenEquiv_aut (x : N) :
    eigenEquiv hinv hexp ht (τ x) =
      ((eigenEquiv hinv hexp ht x).1, (eigenEquiv hinv hexp ht x).2⁻¹) := by
  apply Prod.ext
  · apply Subtype.ext
    change (τ x * τ (τ x)) ^ t = (x * τ x) ^ t
    rw [hinv, mul_comm]
  · apply Subtype.ext
    change (τ x * (τ (τ x))⁻¹) ^ t = ((x * (τ x)⁻¹) ^ t)⁻¹
    rw [hinv, ← inv_pow]
    congr 1
    rw [mul_inv, inv_inv, mul_comm]

end EigenDecomp

/-! ### Transporting the inversion action through an isomorphism -/

theorem multiplicative_zmod_two_cases (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  fin_cases x <;> decide

/-- `invActionHom` sends the generator of `ℤ/2` to inversion. (Local restatement; the original in
`Order2PSq` is `private`.) -/
theorem invActionHom_ofAdd_one {M : Type*} [CommGroup M] :
    invActionHom M (Multiplicative.ofAdd 1) = invAut M := by
  change invAut M ^ ((1 : ZMod 2).val) = invAut M
  rw [show (1 : ZMod 2).val = 1 from by decide, pow_one]

/-- An isomorphism of commutative groups intertwines their generalized-dihedral semidirect
products `M ⋊[inv] ℤ/2`. -/
noncomputable def genDihCongr {M M' : Type*} [CommGroup M] [CommGroup M'] (θ : M ≃* M') :
    SemidirectProduct M (Multiplicative (ZMod 2)) (invActionHom M) ≃*
      SemidirectProduct M' (Multiplicative (ZMod 2)) (invActionHom M') :=
  semidirectProductCongr θ (MulEquiv.refl _) (by
    intro h
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.refl_apply]
    rcases multiplicative_zmod_two_cases h with rfl | rfl
    · simp
    · rw [invActionHom_ofAdd_one, invActionHom_ofAdd_one, invAut_apply, invAut_apply, map_inv])

/-! ### Recognising the eigenspace factors by cardinality -/

/-- A semidirect product with trivial (subsingleton) normal factor collapses to the acting group. -/
def semidirectUniqueLeft {N G : Type*} [Group N] [Group G] [Subsingleton N]
    {φ : G →* MulAut N} : SemidirectProduct N G φ ≃* G where
  toFun x := x.right
  invFun g := inr g
  left_inv _ := SemidirectProduct.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Every element of `ElemAbelianRep p = (ℤ/p)²` has order dividing `p`. -/
theorem pow_p_elemAbelian {p : ℕ} [Fact p.Prime] (x : ElemAbelianRep p) : x ^ p = 1 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, b⟩ := x
  have hpow : ∀ y : CyclicRep p, y ^ p = 1 := fun y => by
    have h1 : y ^ Fintype.card (Multiplicative (ZMod p)) = 1 := pow_card_eq_one
    rwa [Fintype.card_multiplicative, ZMod.card] at h1
  rw [Prod.pow_mk, hpow, hpow]
  exact Prod.ext rfl rfl

/-- A group of order `p²` in which every element has order dividing `p` is `(ℤ/p)²`. -/
theorem mulEquiv_elemAbelian_of_exp {H : Type*} [Group H] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card H = p ^ 2) (hexp : ∀ x : H, x ^ p = 1) :
    Nonempty (H ≃* ElemAbelianRep p) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rcases prime_sq_classification hcard with hcyc | h
  · exfalso
    obtain ⟨e⟩ := hcyc
    have hgen : orderOf (e.symm (Multiplicative.ofAdd (1 : ZMod (p ^ 2)))) = p ^ 2 := by
      rw [show e.symm (Multiplicative.ofAdd (1 : ZMod (p ^ 2)))
            = e.symm.toMonoidHom (Multiplicative.ofAdd 1) from rfl,
        orderOf_injective e.symm.toMonoidHom e.symm.injective,
        orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
    have hdvd : p ^ 2 ∣ p :=
      hgen ▸ orderOf_dvd_of_pow_eq_one (hexp (e.symm (Multiplicative.ofAdd 1)))
    have := Nat.le_of_dvd hp.pos hdvd
    nlinarith [hp.two_le]
  · exact h

/-! ### The generalized dihedral group of a cyclic group is dihedral -/

/-- `ℤ/n ⋊[inversion] ℤ/2 ≅ D_n` for any `n`. -/
noncomputable def genDihedralCyclicIso (n : ℕ) [NeZero n] :
    CyclicRep n ⋊[invActionHom (CyclicRep n)] Multiplicative (ZMod 2) ≃* DihedralGroup n := by
  let fn : CyclicRep n →* DihedralGroup n :=
    { toFun := fun x => DihedralGroup.r (Multiplicative.toAdd x)
      map_one' := by simp
      map_mul' x y := by simp [DihedralGroup.r_mul_r, toAdd_mul] }
  let fg : Multiplicative (ZMod 2) →* DihedralGroup n :=
    { toFun := fun x => if x = 1 then 1 else DihedralGroup.sr 0
      map_one' := by simp
      map_mul' a b := by
        rcases multiplicative_zmod_two_cases a with rfl | rfl
        · simp
        · rcases multiplicative_zmod_two_cases b with rfl | rfl
          · simp
          · have h_prod : Multiplicative.ofAdd (1 : ZMod 2) *
              Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide
            simp [h_prod] }
  have hcompat : ∀ g : Multiplicative (ZMod 2),
      fn.comp ((invActionHom (CyclicRep n)) g).toMonoidHom =
        (MulAut.conj (fg g)).toMonoidHom.comp fn := by
    intro g
    rcases multiplicative_zmod_two_cases g with rfl | rfl
    · ext x; simp [fn, fg]
    · ext x
      simp [fn, fg, invAut_apply,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr]
  let f := SemidirectProduct.lift fn fg hcompat
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rcases x with ⟨m, g⟩
    have hfn_fg : fn m * fg g = 1 := hx
    rcases multiplicative_zmod_two_cases g with rfl | rfl
    · simp only [fn, fg] at hfn_fg
      have h_add_zero : Multiplicative.toAdd m = (0 : ZMod n) := by
        have hr_eq : DihedralGroup.r (Multiplicative.toAdd m) = DihedralGroup.r (0 : ZMod n) := by
          simpa [DihedralGroup.r_zero] using hfn_fg
        exact DihedralGroup.r.inj hr_eq
      have hm : m = 1 := Multiplicative.toAdd.injective (by simpa using h_add_zero)
      simp [hm]
    · have hcalc : fn m * fg (Multiplicative.ofAdd 1) =
          DihedralGroup.sr (-Multiplicative.toAdd m) := by
        simp [fn, fg, DihedralGroup.r_mul_sr]
      rw [hcalc] at hfn_fg
      have : DihedralGroup.sr (-Multiplicative.toAdd m) ≠ (1 : DihedralGroup n) := by
        intro h_eq; cases h_eq
      exact absurd hfn_fg this
  haveI : Finite (CyclicRep n ⋊[invActionHom (CyclicRep n)] Multiplicative (ZMod 2)) :=
    Finite.of_equiv (CyclicRep n × Multiplicative (ZMod 2)) SemidirectProduct.equivProd.symm
  haveI : Fintype (CyclicRep n ⋊[invActionHom (CyclicRep n)] Multiplicative (ZMod 2)) :=
    Fintype.ofFinite _
  haveI : Fintype (DihedralGroup n) := inferInstance
  have hcard_nat : Nat.card (CyclicRep n ⋊[invActionHom (CyclicRep n)] Multiplicative (ZMod 2))
      = Nat.card (DihedralGroup n) := by
    rw [SemidirectProduct.card, card_cyclicRep (NeZero.ne n), Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card, DihedralGroup.nat_card]
    ring
  have hcard_fintype :
      Fintype.card (CyclicRep n ⋊[invActionHom (CyclicRep n)] Multiplicative (ZMod 2))
        = Fintype.card (DihedralGroup n) := by
    simpa [Nat.card_eq_fintype_card] using hcard_nat
  exact MulEquiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard_fintype⟩)

/-! ### CRT isomorphism for the `R2` case -/

/-- `ℤ/p × ℤ/2 ≅ ℤ/2p` (`p` odd prime). -/
noncomputable def crtProdTwo {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Multiplicative (ZMod p) × Multiplicative (ZMod 2) ≃* Multiplicative (ZMod (2 * p)) := by
  have hp : p.Prime := Fact.out
  have hcop : (p).Coprime 2 :=
    hp.coprime_iff_not_dvd.mpr fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  let e_crt : ZMod (p * 2) ≃+* ZMod p × ZMod 2 := ZMod.chineseRemainder hcop
  let e_add : Multiplicative (ZMod (p * 2)) ≃* Multiplicative (ZMod p × ZMod 2) :=
    AddEquiv.toMultiplicative e_crt.toAddEquiv
  let e_prod : Multiplicative (ZMod p × ZMod 2) ≃*
      Multiplicative (ZMod p) × Multiplicative (ZMod 2) :=
    MulEquiv.prodMultiplicative (ZMod p) (ZMod 2)
  let e_mul : Multiplicative (ZMod (2 * p)) ≃* Multiplicative (ZMod (p * 2)) := by
    refine AddEquiv.toMultiplicative (ZMod.ringEquivCongr ?_).toAddEquiv
    ring
  exact (e_prod.symm.trans (e_add.symm.trans e_mul.symm))

/-! ### Assembling the decomposition of the whole group -/

/-- **Elementary-abelian reduction.** If `N` is a commutative group of exponent `p` (`p` odd,
`2t = p+1`) and `φ` is the action of `ℤ/2` whose generator is the involution `τ`, then
`N ⋊[φ] ℤ/2 ≅ fixSubgroup τ × (negSubgroup τ ⋊[inv] ℤ/2)`. -/
noncomputable def elem_decomp_semidirect {N : Type*} [CommGroup N] {p t : ℕ}
    {τ : MulAut N} (hinv : ∀ x, τ (τ x) = x) (hexp : ∀ x : N, x ^ p = 1) (ht : 2 * t = p + 1)
    (φ : Multiplicative (ZMod 2) →* MulAut N) (hφ : φ (Multiplicative.ofAdd 1) = τ) :
    SemidirectProduct N (Multiplicative (ZMod 2)) φ ≃*
      (fixSubgroup τ) × SemidirectProduct (negSubgroup τ) (Multiplicative (ZMod 2))
        (invActionHom (negSubgroup τ)) :=
  (semidirectProductCongr (eigenEquiv hinv hexp ht) (MulEquiv.refl _) (by
    intro h
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.refl_apply]
    rcases multiplicative_zmod_two_cases h with rfl | rfl
    · simp
    · rw [hφ, eigenEquiv_aut hinv hexp ht, prodTrivialAction_apply, invActionHom_ofAdd_one,
        invAut_apply])).trans
    (semidirectProdSplit (invActionHom (negSubgroup τ)))

/-- **Elementary-abelian Sylow case.** A group of order `2p²` whose Sylow-`p` subgroup is `(ℤ/p)²`
is isomorphic to one of `R2`, `R4`, `R5`, according to whether the involution fixes everything, a
line, or nothing. -/
theorem order2psq_elemCase {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (φ : Multiplicative (ZMod 2) →* MulAut (ElemAbelianRep p))
    (hGiso : Nonempty (G ≃* SemidirectProduct (ElemAbelianRep p) (Multiplicative (ZMod 2)) φ)) :
    Nonempty (G ≃* R2 p) ∨ Nonempty (G ≃* R4 p) ∨ Nonempty (G ≃* R5 p) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨eG⟩ := hGiso
  set τ := φ (Multiplicative.ofAdd 1) with hτ
  -- `τ` is an involution.
  have h2 : τ * τ = 1 := by
    rw [← sq, hτ, ← map_pow, show (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 from by decide,
      map_one]
  have hinv : ∀ x, τ (τ x) = x := fun x => by
    have hx := DFunLike.congr_fun h2 x
    rwa [MulAut.mul_apply, MulAut.one_apply] at hx
  have hexp : ∀ x : ElemAbelianRep p, x ^ p = 1 := pow_p_elemAbelian
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have ht : 2 * (m + 1) = p + 1 := by omega
  -- exponent `p` passes to the eigenspaces
  have expFix : ∀ x : fixSubgroup τ, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hexp _)
  have expNeg : ∀ x : negSubgroup τ, x ^ p = 1 := fun x =>
    Subtype.ext (by rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hexp _)
  -- the master decomposition `G ≅ Fix × (Neg ⋊ ℤ/2)`
  let eMain : G ≃* fixSubgroup τ ×
      SemidirectProduct (negSubgroup τ) (Multiplicative (ZMod 2)) (invActionHom (negSubgroup τ)) :=
    eG.trans (elem_decomp_semidirect hinv hexp ht φ rfl)
  -- cardinalities
  have hsplit : Nat.card (fixSubgroup τ) * Nat.card (negSubgroup τ) = p ^ 2 := by
    rw [← Nat.card_prod, ← Nat.card_congr (eigenEquiv hinv hexp ht).toEquiv]
    exact card_elemAbelianRep hp.ne_zero
  have hd_dvd : Nat.card (negSubgroup τ) ∣ p ^ 2 :=
    ⟨Nat.card (fixSubgroup τ), by rw [mul_comm]; exact hsplit.symm⟩
  obtain ⟨i, hi_le, hi⟩ := (Nat.dvd_prime_pow hp).mp hd_dvd
  interval_cases i
  · -- `|Neg| = 1`: trivial action → `R2`
    have hNeg1 : Nat.card (negSubgroup τ) = 1 := by simpa using hi
    haveI : Subsingleton (negSubgroup τ) := (Nat.card_eq_one_iff_unique.mp hNeg1).1
    have hFixSq : Nat.card (fixSubgroup τ) = p ^ 2 := by
      have h := hsplit; rwa [hNeg1, mul_one] at h
    obtain ⟨eFix⟩ := mulEquiv_elemAbelian_of_exp hFixSq expFix
    exact Or.inl ⟨eMain.trans <|
      (MulEquiv.prodCongr eFix semidirectUniqueLeft).trans <|
      (MulEquiv.prodAssoc (M := Multiplicative (ZMod p)) (N := Multiplicative (ZMod p))
        (P := Multiplicative (ZMod 2))).trans <|
      MulEquiv.prodCongr (MulEquiv.refl _) (crtProdTwo hp2)⟩
  · -- `|Neg| = p`: `R4 = D_p × ℤ/p`
    have hNegP : Nat.card (negSubgroup τ) = p := by simpa using hi
    have hFixP : Nat.card (fixSubgroup τ) = p :=
      Nat.eq_of_mul_eq_mul_right hp.pos (by rw [(by rwa [hNegP] at hsplit : _ * p = p ^ 2)]; ring)
    obtain ⟨eFix⟩ := prime_classification hp hFixP
    obtain ⟨eNegC⟩ := prime_classification hp hNegP
    exact Or.inr (Or.inl ⟨eMain.trans <|
      (MulEquiv.prodCongr eFix ((genDihCongr eNegC).trans (genDihedralCyclicIso p))).trans <|
      MulEquiv.prodComm (M := CyclicRep p) (N := DihedralGroup p)⟩)
  · -- `|Neg| = p²`: `R5`, the generalized dihedral group
    have hNegSq : Nat.card (negSubgroup τ) = p ^ 2 := by simpa using hi
    have hFix1 : Nat.card (fixSubgroup τ) = 1 :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2)
        (by rw [one_mul, (by rwa [hNegSq] at hsplit : _ * p ^ 2 = p ^ 2)])
    haveI : Subsingleton (fixSubgroup τ) := (Nat.card_eq_one_iff_unique.mp hFix1).1
    haveI : Unique (fixSubgroup τ) := uniqueOfSubsingleton 1
    obtain ⟨eNegE⟩ := mulEquiv_elemAbelian_of_exp hNegSq expNeg
    exact Or.inr (Or.inr ⟨eMain.trans <|
      MulEquiv.uniqueProd.trans <|
      genDihCongr (eNegE.trans (MulEquiv.prodMultiplicative (ZMod p) (ZMod p)).symm)⟩)

/-! ### Full classification of groups of order `2p²` -/

/-- **Classification of groups of order `2p²` (`p` an odd prime).** Every such group is isomorphic
to exactly one of the five representatives `R1 = ℤ/2p²`, `R2 = ℤ/p × ℤ/2p`, `R3 = D_{p²}`,
`R4 = D_p × ℤ/p`, `R5 = (ℤ/p)² ⋊₋₁ ℤ/2`. (Pairwise non-isomorphism is `all_pairwise`.) -/
theorem order2psq_classification {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    [Finite G] (hG : Nat.card G = 2 * p ^ 2) :
    Nonempty (G ≃* R1 p) ∨ Nonempty (G ≃* R2 p) ∨ Nonempty (G ≃* R3 p) ∨
      Nonempty (G ≃* R4 p) ∨ Nonempty (G ≃* R5 p) := by
  rcases order2psq_semidirect hp2 hG with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · rcases order2psq_cyclicCase hp2 φ hφ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases order2psq_elemCase hp2 φ hφ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- **The five representatives are a complete, non-redundant classification of order `2p²`.**
Bundles exhaustiveness (`order2psq_classification`), the cardinalities, and the ten pairwise
non-isomorphism facts into an `IsClassif`. -/
theorem order2psq_isClassif {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {N : ℕ} (hN : 2 * p ^ 2 = N) :
    IsClassif N (rep5 (R1 p) (R2 p) (R3 p) (R4 p) (R5 p)) := by
  subst hN
  have hp : p.Prime := Fact.out
  refine isClassif_five (R1 p) (R2 p) (R3 p) (R4 p) (R5 p)
    (card_R1 p) (card_R2 p) (card_R3 p) (card_R4 p) (card_R5 p)
    (fun G _ hG => ?_)
    (fun h => absurd (abelianFam_pairwise (p := p) 0 1 h) (by decide))
    (abelian_nonab_disjoint hp2 0 0) (abelian_nonab_disjoint hp2 0 1)
    (abelian_nonab_disjoint hp2 0 2) (abelian_nonab_disjoint hp2 1 0)
    (abelian_nonab_disjoint hp2 1 1) (abelian_nonab_disjoint hp2 1 2)
    (fun h => absurd (nonabFam_pairwise hp2 0 1 h) (by decide))
    (fun h => absurd (nonabFam_pairwise hp2 0 2 h) (by decide))
    (fun h => absurd (nonabFam_pairwise hp2 1 2 h) (by decide))
  haveI : Finite G := Nat.finite_of_card_ne_zero
    (by rw [hG]; exact Nat.mul_ne_zero two_ne_zero (pow_ne_zero 2 hp.ne_zero))
  exact order2psq_classification hp2 hG

end Smallgroups.UsefulTheorems
