/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order24
import Smallgroups.UsefulTheorems.Order36
import Smallgroups.UsefulTheorems.Order72.P9xH8_D4
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
open Finset

/-!
# Groups of order 72: the residual case `n₃ = 4`, `n₂ ≠ 1`

This file classifies the groups of order `72` with four Sylow `3`-subgroups and
non-normal Sylow `2`-subgroups.  There are exactly **four** such groups
(GAP `#15, 42, 43, 44`):

* `order72_res_S3xA4`: `S3 × A4` (GAP `#44`), the only one with a kernel of order `6`;
* `order72_res_C3xS4`: `C3 × S4` (GAP `#42`);
* `order72_res_C3sS4`: `C3 ⋊ S4` via the sign action (GAP `#43`);
* `order72_res_C3S4`: the non-split `C3.S4` (GAP `#15`), built as the Goursat
  (fiber-product) kernel of `D9 × S4 → S3`.

The analysis: `G` acts by conjugation on the four Sylow `3`-subgroups; the kernel `K`
of the permutation action has order `3` or `6` and the image is `S4` or `A4`
(`order72_sylow_3_conj_action_of_card_sylow_3_eq_four`).  The order-`6` kernel is `S3`
(an order-`6` cyclic kernel forces a normal Sylow `2` via the order-`36`
classification) and gives `G ≅ S3 × A4` by centralizing.  The order-`3` kernel gives
`G/K ≅ S4`; the `C2²` under the Klein group of `S4` is normal in `G`, the quotient is
a nonabelian group of order `18`, and `G` is recovered as the corresponding fiber
product over the common `S3`-quotient.
-/

namespace Smallgroups.UsefulTheorems

open P3Group

variable {G : Type} [Group G]

/-! ### The four residual representatives

The residual case `n₃ = 4 ∧ n₂ ≠ 1` contributes exactly four isomorphism classes
(GAP `#15, 42, 43, 44`):

* `order72_res_S3xA4` : `S₃ × A₄` (GAP `#44`) — the `|ker ψ| = 6` branch;
* `order72_res_C3xS4` : `C₃ × S₄` (GAP `#42`);
* `order72_res_C3sS4` : `C₃ ⋊[sign] S₄` (GAP `#43`);
* `order72_res_C3S4`  : the non-split `C₃.S₄` (GAP `#15`), the Goursat kernel of
  `D₉ × S₄ → S₃`. -/

abbrev order72_C3 : Type := CyclicRep 3
abbrev order72_C9 : Type := CyclicRep 9
abbrev order72_S4 : Type := Equiv.Perm (Fin 4)

/-- `S₃ × A₄`. -/
abbrev order72_res_S3xA4 : Type := DihedralGroup 3 × alternatingGroup (Fin 4)

/-- `C₃ × S₄`. -/
abbrev order72_res_C3xS4 : Type := order72_C3 × order72_S4

/-- The sign character `S₄ →* (ℤ/3)ˣ`, obtained by casting the sign `±1` into
`(ℤ/3)ˣ`. -/
noncomputable abbrev order72_S4_signToZmod3 : order72_S4 →* (ZMod 3)ˣ :=
  MonoidHom.comp
    (Units.map (show MonoidHom ℤ (ZMod 3) from (Int.castRingHom (ZMod 3)).toMonoidHom))
    Equiv.Perm.sign

/-- The split `C₃ ⋊ S₄` via the sign action: `S₄ →* Aut(C₃)` factors through the
sign, landing in `{±1} ⊆ Aut(C₃)`. -/
noncomputable abbrev order72_C3S4_signAction : order72_S4 →* MulAut (CyclicRep 3) :=
  unitAutHom.comp order72_S4_signToZmod3

/-- The split `C₃ ⋊ S₄` (GAP `#43`). -/
abbrev order72_res_C3sS4 : Type :=
  SemidirectProduct (CyclicRep 3) order72_S4 order72_C3S4_signAction

/-- The non-split `C₃.S₄` (GAP `#15`): the Goursat fiber product of
`D₉ → S₃` (quotient by the rotation subgroup of order `3`) and
`S₄ → S₃` (quotient by the Klein four `V₄`). Concretely it is the subgroup
`{ (x, g) : D₉ × S₄ | x·C₃ = g·V₄ }` of order `72`. -/
abbrev order72_D9 : Type := DihedralGroup 9

/-- The quotient homomorphism `D₉ → S₃` collapsing the rotation subgroup of
order `9` onto its quotient of order `3`. Its kernel is `⟨r³⟩`. -/
noncomputable def order72_D9ToS3 : order72_D9 →* DihedralGroup 3 :=
  let φ : ZMod 9 →+ ZMod 3 :=
    (ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3)).toAddMonoidHom
  MonoidHom.mk'
    (fun x => match x with
      | DihedralGroup.r i => DihedralGroup.r (φ i)
      | DihedralGroup.sr i => DihedralGroup.sr (φ i))
    (by intro x y; cases x <;> cases y <;> simp [φ.map_add,
      DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr])

/-- The Klein four `V₄` as a normal subgroup of `S₄`. -/
noncomputable def order72_S4_V4 : Subgroup order72_S4 :=
  Subgroup.map (alternatingGroup (Fin 4)).subtype
    (alternatingGroup.kleinFour (Fin 4))

/-- The three pairings (partitions into two pairs) of `{0,1,2,3}`. -/
def order72_S4_pairings : Fin 3 → Finset (Finset (Fin 4)) :=
  let f2 (a b : Fin 4) : Finset (Fin 4) := insert a (singleton b)
  ![ insert (f2 0 1) (singleton (f2 2 3)),
     insert (f2 0 2) (singleton (f2 1 3)),
     insert (f2 0 3) (singleton (f2 1 2)) ]

/-- The index of the pairing in which `0` is paired with `a`.
The value at `a = 0` is irrelevant in the applications below. -/
def order72_S4_partnerIndex (a : Fin 4) : Fin 3 :=
  if a = 1 then 0 else if a = 2 then 1 else 2

/-- In the `i`-th pairing, return the element paired with `a`. -/
def order72_S4_pairingPartner (i : Fin 3) (a : Fin 4) : Fin 4 :=
  if i = 0 then
    if a = 0 then 1 else if a = 1 then 0 else if a = 2 then 3 else 2
  else if i = 1 then
    if a = 0 then 2 else if a = 2 then 0 else if a = 1 then 3 else 1
  else
    if a = 0 then 3 else if a = 3 then 0 else if a = 1 then 2 else 1

/-- The action of `S₄` on the three pairings, returning the target pairing index. -/
def order72_S4_pairingAct (σ : order72_S4) (i : Fin 3) : Fin 3 :=
  order72_S4_partnerIndex (σ (order72_S4_pairingPartner i (σ.symm 0)))

/-- The action of `S₄` on the three pairings, as a permutation of `Fin 3`. -/
noncomputable def order72_S4_pairingActPerm (σ : order72_S4) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (order72_S4_pairingAct σ)
    (by
      -- The image of a pairing under a permutation σ is again one of the three
      -- pairings, so `pairingAct σ` permutes `Fin 3`; its inverse is `pairingAct σ.symm`.
      classical
      revert σ
      decide)

set_option maxRecDepth 10000 in
/-- `S₄` acts on the three pairings, giving a homomorphism `S₄ → S₃`. -/
noncomputable def order72_S4ToS3_perm : order72_S4 →* Equiv.Perm (Fin 3) :=
  MonoidHom.mk' order72_S4_pairingActPerm
    (by
      intro σ τ
      ext i
      revert σ τ i
      decide)

/-- The canonical isomorphism `S₃ ≅ D₃`. -/
private noncomputable def order72_d3_to_perm3 : DihedralGroup 3 →* Equiv.Perm (Fin 3) :=
  MonoidHom.mk'
    (fun x =>
      Equiv.ofBijective
        (fun a : Fin 3 =>
          (ZMod.finEquiv 3).symm <|
            match x with
            | DihedralGroup.r i => (ZMod.finEquiv 3 a) - i
            | DihedralGroup.sr i => i - (ZMod.finEquiv 3 a))
        (by
          cases x <;>
          decide +revert))
    (by
      intro x y
      cases x <;> cases y <;> ext a <;> decide +revert)

/-- The canonical isomorphism `S₃ ≅ D₃`, with `D₃` acting on the three vertices. -/
noncomputable def order72_perm3_to_d3 : Equiv.Perm (Fin 3) ≃* DihedralGroup 3 :=
  (MulEquiv.ofBijective order72_d3_to_perm3 (by decide +revert)).symm

/-- The quotient `S₄ / V₄ ≅ S₃ ≅ D₃`. -/
noncomputable def order72_S4ToS3 : order72_S4 →* DihedralGroup 3 :=
  order72_perm3_to_d3.toMonoidHom.comp order72_S4ToS3_perm

/-- The `D₉ → S₃` quotient, with `S₃` represented as permutations of three points. -/
private noncomputable def order72_D9ToS3_perm : order72_D9 →* Equiv.Perm (Fin 3) :=
  order72_d3_to_perm3.comp order72_D9ToS3

/-- The non-split `C₃.S₄` (GAP `#15`), as a subgroup of `D₉ × S₄`. -/
noncomputable def order72_res_C3S4_subgroup : Subgroup (order72_D9 × order72_S4) where
  carrier := { p | order72_D9ToS3_perm p.1 = order72_S4ToS3_perm p.2 }
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change order72_D9ToS3_perm x.1 = order72_S4ToS3_perm x.2 at hx
    change order72_D9ToS3_perm y.1 = order72_S4ToS3_perm y.2 at hy
    simp [hx, hy]
  inv_mem' := by
    intro x hx
    change order72_D9ToS3_perm x.1 = order72_S4ToS3_perm x.2 at hx
    simp [hx]

/-- The non-split `C₃.S₄` (GAP `#15`), as a group. -/
abbrev order72_res_C3S4 : Type := order72_res_C3S4_subgroup

/-- Membership in the Goursat subgroup `order72_res_C3S4_subgroup` is decidable (it is an
equation between permutations of three points). -/
noncomputable instance instDecidableMemOrder72ResC3S4 (p : order72_D9 × order72_S4) :
    Decidable (p ∈ order72_res_C3S4_subgroup) :=
  decidable_of_iff (order72_D9ToS3_perm p.1 = order72_S4ToS3_perm p.2) Iff.rfl

/-- The Goursat subgroup is finite, with a computable enumeration. -/
noncomputable instance instFintypeOrder72ResC3S4 : Fintype ↥order72_res_C3S4_subgroup :=
  Subtype.fintype _


theorem card_order72_res_S3xA4 : Nat.card order72_res_S3xA4 = 72 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, DihedralGroup.card,
    nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

theorem card_order72_res_C3xS4 : Nat.card order72_res_C3xS4 = 72 := by
  rw [Nat.card_prod, show Nat.card (CyclicRep 3) = 3 from card_cyclicRep (by norm_num),
    Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]

theorem card_order72_res_C3sS4 : Nat.card order72_res_C3sS4 = 72 := by
  rw [SemidirectProduct.card,
    show Nat.card (CyclicRep 3) = 3 from card_cyclicRep (by norm_num),
    Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]

private theorem card_order72_res_C3S4_raw :
    Nat.card { p : order72_D9 × order72_S4 //
      order72_D9ToS3_perm p.1 = order72_S4ToS3_perm p.2 } = 72 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem card_order72_res_C3S4 : Nat.card order72_res_C3S4 = 72 := by
  classical
  exact (Nat.card_congr (Equiv.subtypeEquivRight (fun p : order72_D9 × order72_S4 => by
    rfl))).trans card_order72_res_C3S4_raw

/-- The four representatives in the residual branch, indexed in the GAP order
`#15, #42, #43, #44`. -/
abbrev order72ResidualRep : Fin 4 → Type
  | 0 => order72_res_C3S4
  | 1 => order72_res_C3xS4
  | 2 => order72_res_C3sS4
  | 3 => order72_res_S3xA4

noncomputable instance instGroupOrder72ResidualRep : (i : Fin 4) → Group (order72ResidualRep i)
  | ⟨0, _⟩ => inferInstance
  | ⟨1, _⟩ => inferInstance
  | ⟨2, _⟩ => inferInstance
  | ⟨3, _⟩ => inferInstance
  | ⟨n + 4, h⟩ => by omega

theorem card_order72ResidualRep (i : Fin 4) : Nat.card (order72ResidualRep i) = 72 := by
  fin_cases i
  · exact card_order72_res_C3S4
  · exact card_order72_res_C3xS4
  · exact card_order72_res_C3sS4
  · exact card_order72_res_S3xA4

/-- The target representative alternatives for the residual branch. -/
abbrev order72ResidualRepCases (G : Type*) [Group G] : Prop :=
  Nonempty (G ≃* order72_res_C3S4) ∨
    Nonempty (G ≃* order72_res_C3xS4) ∨
      Nonempty (G ≃* order72_res_C3sS4) ∨
        Nonempty (G ≃* order72_res_S3xA4)

theorem order72ResidualRepCases_iff_exists_index {G : Type*} [Group G] :
    order72ResidualRepCases G ↔ ∃ i : Fin 4, Nonempty (G ≃* order72ResidualRep i) := by
  constructor
  · intro h
    rcases h with h0 | h1 | h2 | h3
    · exact ⟨0, by simpa [order72ResidualRep] using h0⟩
    · exact ⟨1, by simpa [order72ResidualRep] using h1⟩
    · exact ⟨2, by simpa [order72ResidualRep] using h2⟩
    · exact ⟨3, by simpa [order72ResidualRep] using h3⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (by simpa [order72ResidualRep] using hi)
    · exact Or.inr (Or.inl (by simpa [order72ResidualRep] using hi))
    · exact Or.inr (Or.inr (Or.inl (by simpa [order72ResidualRep] using hi)))
    · exact Or.inr (Or.inr (Or.inr (by simpa [order72ResidualRep] using hi)))

theorem card_of_order72ResidualRepCases {G : Type*} [Group G]
    (h : order72ResidualRepCases G) : Nat.card G = 72 := by
  rcases h with hC3S4 | hC3xS4 | hC3sS4 | hS3xA4
  · obtain ⟨e⟩ := hC3S4
    exact (Nat.card_congr e.toEquiv).trans card_order72_res_C3S4
  · obtain ⟨e⟩ := hC3xS4
    exact (Nat.card_congr e.toEquiv).trans card_order72_res_C3xS4
  · obtain ⟨e⟩ := hC3sS4
    exact (Nat.card_congr e.toEquiv).trans card_order72_res_C3sS4
  · obtain ⟨e⟩ := hS3xA4
    exact (Nat.card_congr e.toEquiv).trans card_order72_res_S3xA4

theorem card_of_order72ResidualRepIndex {G : Type*} [Group G]
    (h : ∃ i : Fin 4, Nonempty (G ≃* order72ResidualRep i)) : Nat.card G = 72 :=
  card_of_order72ResidualRepCases (order72ResidualRepCases_iff_exists_index.mpr h)

/-- If there are four Sylow `3`-subgroups in a group of order `72`, each Sylow
`3`-normalizer has order `18`. -/
theorem order72_card_normalizer_sylow_three_of_card_sylow_3_eq_four [Finite G]
    (hG : Nat.card G = 72) (hSyl : Nat.card (Sylow 3 G) = 4) (P : Sylow 3 G) :
    Nat.card (Subgroup.normalizer (P : Set G)) = 18 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hidx : (Subgroup.normalizer (P : Set G)).index = 4 := by
    rwa [← Sylow.card_eq_index_normalizer P]
  have := (Subgroup.normalizer (P : Set G)).card_mul_index
  rw [hidx, hG] at this
  omega

/-- **Kernel analysis of the residual case**: the conjugation action of `G` on its
four Sylow `3`-subgroups has kernel of order `3` with image `S4`, or kernel of order
`6` with image `A4`. -/
theorem order72_sylow_3_conj_action_of_card_sylow_3_eq_four [Finite G]
    (hG : Nat.card G = 72) (hSyl : Nat.card (Sylow 3 G) = 4) :
    ∃ ψ : G →* Equiv.Perm (Fin 4),
      (Nat.card ψ.ker = 3 ∧ ψ.range = ⊤) ∨
        (Nat.card ψ.ker = 6 ∧ ψ.range = alternatingGroup (Fin 4)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  have hfincard : Fintype.card (Sylow 3 G) = 4 := by
    rwa [← Nat.card_eq_fintype_card]
  let ε : Sylow 3 G ≃ Fin 4 := by rw [← hfincard]; exact Fintype.equivFin _
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
  have hcardNorm : Nat.card (Subgroup.normalizer (P0 : Set G)) = 18 :=
    order72_card_normalizer_sylow_three_of_card_sylow_3_eq_four hG hSyl P0
  have hker_card_dvd : Nat.card ψ.ker ∣ 18 :=
    hcardNorm ▸ Subgroup.card_dvd_of_le hker_le
  have hker_card_ne_nine : Nat.card ψ.ker ≠ 9 := by
    intro hker9
    -- `K` is a `3`-subgroup, hence contained in a Sylow `3`, forcing it normal.
    have hpK : IsPGroup 3 ↥ψ.ker := IsPGroup.iff_card.mpr ⟨2, hker9⟩
    obtain ⟨Q, hQ⟩ := hpK.exists_le_sylow
    have hker_eq : ψ.ker = ↑Q := by
      have hcardQ : Nat.card (↑Q : Subgroup G) = 9 :=
        card_sylow_three_subgroup_of_card_72 hG Q
      exact Subgroup.eq_of_le_of_card_ge hQ (by rw [hker9, hcardQ])
    have hQn : (↑Q : Subgroup G).Normal := hker_eq ▸ MonoidHom.normal_ker ψ
    haveI := Sylow.unique_of_normal Q hQn
    have : Nat.card (Sylow 3 G) = 1 := Nat.card_unique
    omega
  have hker_card_ne_eighteen : Nat.card ψ.ker ≠ 18 := by
    intro hker18
    have hker_eq : ψ.ker = Subgroup.normalizer (P0 : Set G) :=
      Subgroup.eq_of_le_of_card_ge hker_le (by rw [hcardNorm, hker18])
    have hNn : (Subgroup.normalizer (P0 : Set G)).Normal := hker_eq ▸ MonoidHom.normal_ker ψ
    have hPn := Sylow.normal_of_normalizer_normal P0 hNn
    haveI := Sylow.unique_of_normal P0 hPn
    have : Nat.card (Sylow 3 G) = 1 := Nat.card_unique
    omega
  have hker_card_ge : 3 ≤ Nat.card ψ.ker := by
    -- the image has order `72/|K|` and embeds in `S4`, hence is at most `24`.
    have hidx : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
    have hmul := ψ.ker.card_mul_index
    rw [hidx, hG] at hmul
    have hrange_dvd : Nat.card ψ.range ∣ Nat.card (Equiv.Perm (Fin 4)) :=
      Subgroup.card_subgroup_dvd_card ψ.range
    have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_perm, Nat.card_fin]
      decide
    rw [hperm] at hrange_dvd
    have hle : Nat.card ψ.range ≤ 24 := Nat.le_of_dvd (by norm_num) hrange_dvd
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    by_contra hc
    push Not at hc
    interval_cases h : Nat.card ψ.ker <;> omega
  have hker_card : Nat.card ψ.ker = 3 ∨ Nat.card ψ.ker = 6 := by
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    have hle : Nat.card ψ.ker ≤ 18 := Nat.le_of_dvd (by norm_num) hker_card_dvd
    have hge3 := hker_card_ge
    interval_cases h : Nat.card ψ.ker
    · exact Or.inl rfl
    · exfalso
      norm_num at hker_card_dvd
    · exfalso
      norm_num at hker_card_dvd
    · exact Or.inr rfl
    · exfalso
      norm_num at hker_card_dvd
    · exfalso
      norm_num at hker_card_dvd
    · exact absurd rfl hker_card_ne_nine
    · exfalso
      norm_num at hker_card_dvd
    · exfalso
      norm_num at hker_card_dvd
    · exfalso
      norm_num at hker_card_dvd
    · exfalso
      norm_num at hker_card_dvd
    · exfalso
      norm_num at hker_card_dvd
    · exfalso
      norm_num at hker_card_dvd
    · exfalso
      norm_num at hker_card_dvd
    · exfalso
      norm_num at hker_card_dvd
    · exact absurd rfl hker_card_ne_eighteen
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  rcases hker_card with hker3 | hker6
  · have hidx : ψ.ker.index = 24 := by
      have := ψ.ker.card_mul_index
      rw [hker3, hG] at this
      omega
    have hcard_range : Nat.card ψ.range = 24 := by
      rw [← Subgroup.index_ker ψ, hidx]
    exact ⟨ψ, Or.inl ⟨hker3,
      Subgroup.eq_top_of_card_eq ψ.range (by rw [hcard_range, hperm])⟩⟩
  · have hidx : ψ.ker.index = 12 := by
      have := ψ.ker.card_mul_index
      rw [hker6, hG] at this
      omega
    have hcard_range : Nat.card ψ.range = 12 := by
      rw [← Subgroup.index_ker ψ, hidx]
    have h_range_idx : ψ.range.index = 2 := by
      have := ψ.range.card_mul_index
      rw [hcard_range, hperm] at this
      omega
    exact ⟨ψ, Or.inr ⟨hker6,
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two h_range_idx⟩⟩

/-- The current structural endpoint for the residual branch: `n₂ ≠ 1`, and the
conjugation action on the four Sylow `3`-subgroups has kernel/image data of the expected
two types. -/
abbrev order72ResidualKernelCases (G : Type*) [Group G] [Finite G] : Prop :=
  Nat.card (Sylow 2 G) ≠ 1 ∧
    ∃ ψ : G →* Equiv.Perm (Fin 4),
      (Nat.card ψ.ker = 3 ∧ ψ.range = ⊤) ∨
        (Nat.card ψ.ker = 6 ∧ ψ.range = alternatingGroup (Fin 4))

theorem order72_residual_kernel_cases_of_residual [Finite G]
    (hG : Nat.card G = 72)
    (hres : Nat.card (Sylow 3 G) = 4 ∧ Nat.card (Sylow 2 G) ≠ 1) :
    order72ResidualKernelCases G :=
  ⟨hres.2, order72_sylow_3_conj_action_of_card_sylow_3_eq_four hG hres.1⟩

/-- Current global assembly for order `72`: the Sylow-`3`-normal branch is completely
classified, the Sylow-`2`-normal branch is classified, and the only remaining branch is
reduced to the kernel/image analysis of the action on the four Sylow `3`-subgroups. -/
theorem order72_current_classification_reduction [Finite G] (hG : Nat.card G = 72) :
    order72Sylow3NormalSolvedAllCases G ∨
      order72Sylow2NormalRepCases G ∨
        order72ResidualKernelCases G := by
  rcases order72_partial_classification_refined_all_e9_done hG with h3 | h2 | hres
  · exact Or.inl h3
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (order72_residual_kernel_cases_of_residual hG hres))

/-- The final representative alternatives for order `72`, pending the last residual
kernel-to-representative classification. -/
abbrev order72RepCases (G : Type*) [Group G] : Prop :=
  order72Sylow3NormalSolvedAllCases G ∨
    order72Sylow2NormalRepCases G ∨
      order72ResidualRepCases G

/-- Once the residual kernel/image endpoint is converted to the four residual
representatives, the current reduction immediately gives the full order-`72`
representative classification. -/
theorem order72_rep_cases_of_residual_kernel_cases_done
    (hresidual :
      ∀ {G : Type} [Group G] [Finite G],
        Nat.card G = 72 → order72ResidualKernelCases G → order72ResidualRepCases G)
    {G : Type} [Group G] [Finite G] (hG : Nat.card G = 72) :
    order72RepCases G := by
  rcases order72_current_classification_reduction hG with h3 | h2 | hres
  · exact Or.inl h3
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (hresidual hG hres))

end Smallgroups.UsefulTheorems
