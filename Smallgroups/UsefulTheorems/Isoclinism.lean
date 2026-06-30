/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-!
# Isoclinism of groups

Two groups `G₁` and `G₂` are **isoclinic** if there exist isomorphisms
`φ : G₁/Z(G₁) ≃* G₂/Z(G₂)` and `ψ : [G₁,G₁] ≃* [G₂,G₂]` such that
the commutator maps are compatible: `ψ([a₁,b₁]) = [a₂,b₂]` whenever
`φ(a₁ · Z₁) = a₂ · Z₂` and `φ(b₁ · Z₁) = b₂ · Z₂`.

Isoclinism, introduced by Philip Hall (1940), is an equivalence relation coarser than
isomorphism. It partitions groups into **families**; within each family, **stem groups**
(those with `Z(G) ≤ [G,G]`) are the smallest representatives. All abelian groups form a
single isoclinism family.

## Main definitions

* `Isoclinism` — the structure encoding an isoclinism between two groups
* `IsStemGroup` — a group where `Z(G) ≤ [G,G]`

## Main results

* `commutatorElement_mul_center_left/right` — commutator is constant on `Z(G)`-cosets
* `commutatorElement_center_congr` — well-definedness of the commutator map on `G/Z(G)`
* `Isoclinism.refl` — isoclinism is reflexive
* `Isoclinism.symm` — isoclinism is symmetric
* `Isoclinism.trans` — isoclinism is transitive
* `Isoclinism.ofMulEquiv` — isomorphic groups are isoclinic
* `not_isoclinic_of_card_commutator_ne` — groups with different `|[G,G]|` are not isoclinic

## References

* Philip Hall, *The classification of prime-power groups*, 1940
* <https://en.wikipedia.org/wiki/Isoclinism_of_groups>
-/

namespace Smallgroups.UsefulTheorems

open Subgroup
open scoped commutatorElement

/-! ### Commutator elements and the center -/

section CommutatorCenter

variable {G : Type*} [Group G]

/-- Every commutator element lies in the derived subgroup. -/
theorem commutatorElement_mem_commutator' (a b : G) :
    ⁅a, b⁆ ∈ commutator G :=
  commutator_def G ▸ commutator_mem_commutator (mem_top a) (mem_top b)

/-- Multiplying the left argument of a commutator by a central element does not change it. -/
theorem commutatorElement_mul_center_left {a b z : G} (hz : z ∈ center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  have : z * b = b * z := (mem_center_iff.mp hz b).symm
  calc a * z * b * (a * z)⁻¹ * b⁻¹
      = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [this]
    _ = a * b * a⁻¹ * b⁻¹ := by group

/-- Multiplying the right argument of a commutator by a central element does not change it. -/
theorem commutatorElement_mul_center_right {a b z : G} (hz : z ∈ center G) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  have : z * a⁻¹ = a⁻¹ * z := (mem_center_iff.mp hz a⁻¹).symm
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹
      = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [this]
    _ = a * b * a⁻¹ * b⁻¹ := by group

/-- The commutator depends only on `Z(G)`-cosets: if `a₁⁻¹a₂` and `b₁⁻¹b₂` are central,
then `[a₁,b₁] = [a₂,b₂]`. This is the well-definedness condition for the commutator map
on `G/Z(G) × G/Z(G)`. -/
theorem commutatorElement_center_congr {a₁ a₂ b₁ b₂ : G}
    (ha : a₁⁻¹ * a₂ ∈ center G) (hb : b₁⁻¹ * b₂ ∈ center G) :
    ⁅a₁, b₁⁆ = ⁅a₂, b₂⁆ := by
  have ha₂ : a₂ = a₁ * (a₁⁻¹ * a₂) := by group
  have hb₂ : b₂ = b₁ * (b₁⁻¹ * b₂) := by group
  rw [ha₂, hb₂, commutatorElement_mul_center_right hb, commutatorElement_mul_center_left ha]

end CommutatorCenter

/-! ### Isoclinism -/

/-- Two groups are **isoclinic** if there exist isomorphisms between their inner automorphism
groups (quotients by the center) and between their derived subgroups, compatible with the
commutator map.

Concretely, `φ : G₁/Z(G₁) ≃* G₂/Z(G₂)` and `ψ : [G₁,G₁] ≃* [G₂,G₂]` satisfy:
for all `a₁, b₁ ∈ G₁` and `a₂, b₂ ∈ G₂`, if `φ` maps the cosets of `a₁, b₁` to those of
`a₂, b₂`, then `ψ` maps `[a₁,b₁]` to `[a₂,b₂]`. -/
structure Isoclinism (G₁ G₂ : Type*) [Group G₁] [Group G₂] where
  φ : G₁ ⧸ center G₁ ≃* G₂ ⧸ center G₂
  ψ : ↥(commutator G₁) ≃* ↥(commutator G₂)
  comm : ∀ (a₁ b₁ : G₁) (a₂ b₂ : G₂),
    φ (QuotientGroup.mk' (center G₁) a₁) = QuotientGroup.mk' (center G₂) a₂ →
    φ (QuotientGroup.mk' (center G₁) b₁) = QuotientGroup.mk' (center G₂) b₂ →
    ψ ⟨⁅a₁, b₁⁆, commutatorElement_mem_commutator' a₁ b₁⟩ =
      ⟨⁅a₂, b₂⁆, commutatorElement_mem_commutator' a₂ b₂⟩

namespace Isoclinism

/-- Isoclinism is reflexive. -/
def refl (G : Type*) [Group G] : Isoclinism G G where
  φ := MulEquiv.refl _
  ψ := MulEquiv.refl _
  comm a₁ b₁ a₂ b₂ ha hb := by
    simp only [MulEquiv.refl_apply] at ha hb ⊢
    rw [QuotientGroup.mk'_eq_mk'] at ha hb
    obtain ⟨za, hza_mem, hza_eq⟩ := ha
    obtain ⟨zb, hzb_mem, hzb_eq⟩ := hb
    have hmema : a₁⁻¹ * a₂ ∈ center G := by
      have : a₁⁻¹ * a₂ = za := by rw [← hza_eq]; group
      rw [this]; exact hza_mem
    have hmemb : b₁⁻¹ * b₂ ∈ center G := by
      have : b₁⁻¹ * b₂ = zb := by rw [← hzb_eq]; group
      rw [this]; exact hzb_mem
    exact Subtype.ext (commutatorElement_center_congr hmema hmemb)

/-- Isoclinism is symmetric. -/
def symm {G₁ G₂ : Type*} [Group G₁] [Group G₂] (iso : Isoclinism G₁ G₂) :
    Isoclinism G₂ G₁ where
  φ := iso.φ.symm
  ψ := iso.ψ.symm
  comm a₂ b₂ a₁ b₁ ha hb := by
    have ha' : iso.φ (QuotientGroup.mk' (center G₁) a₁) =
               QuotientGroup.mk' (center G₂) a₂ := by
      rw [← ha, MulEquiv.apply_symm_apply]
    have hb' : iso.φ (QuotientGroup.mk' (center G₁) b₁) =
               QuotientGroup.mk' (center G₂) b₂ := by
      rw [← hb, MulEquiv.apply_symm_apply]
    have h := iso.comm a₁ b₁ a₂ b₂ ha' hb'
    rw [← h, iso.ψ.symm_apply_apply]

/-- Isoclinism is transitive. -/
def trans {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
    (iso₁₂ : Isoclinism G₁ G₂) (iso₂₃ : Isoclinism G₂ G₃) : Isoclinism G₁ G₃ where
  φ := iso₁₂.φ.trans iso₂₃.φ
  ψ := iso₁₂.ψ.trans iso₂₃.ψ
  comm a₁ b₁ a₃ b₃ ha hb := by
    simp only [MulEquiv.trans_apply] at ha hb ⊢
    obtain ⟨a₂, ha₂⟩ := QuotientGroup.mk'_surjective (center G₂)
      (iso₁₂.φ (QuotientGroup.mk' (center G₁) a₁))
    obtain ⟨b₂, hb₂⟩ := QuotientGroup.mk'_surjective (center G₂)
      (iso₁₂.φ (QuotientGroup.mk' (center G₁) b₁))
    have ha' : iso₂₃.φ (QuotientGroup.mk' (center G₂) a₂) =
               QuotientGroup.mk' (center G₃) a₃ := by rwa [ha₂]
    have hb' : iso₂₃.φ (QuotientGroup.mk' (center G₂) b₂) =
               QuotientGroup.mk' (center G₃) b₃ := by rwa [hb₂]
    rw [iso₁₂.comm a₁ b₁ a₂ b₂ ha₂.symm hb₂.symm, iso₂₃.comm a₂ b₂ a₃ b₃ ha' hb']

/-- Isomorphic groups are isoclinic. The quotient `G₁/Z(G₁) ≃* G₂/Z(G₂)` and derived subgroup
`[G₁,G₁] ≃* [G₂,G₂]` isomorphisms are induced by `e`. -/
noncomputable def ofMulEquiv {G₁ G₂ : Type*} [Group G₁] [Group G₂] (e : G₁ ≃* G₂) :
    Isoclinism G₁ G₂ := by
  let f : G₁ →* G₂ ⧸ center G₂ := (QuotientGroup.mk' (center G₂)).comp e.toMonoidHom
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center G₂) y
    obtain ⟨x', rfl⟩ := e.surjective x
    exact ⟨x', hx⟩
  have hker : center G₁ = MonoidHom.ker f := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, f]
    constructor
    · intro h
      rw [Subgroup.mem_center_iff] at h
      rw [Subgroup.mem_center_iff]
      intro g₂
      obtain ⟨g, rfl⟩ := e.surjective g₂
      calc e g * e x = e (g * x) := (map_mul e g x).symm
        _ = e (x * g) := by rw [h g]
        _ = e x * e g := map_mul e x g
    · intro h
      rw [Subgroup.mem_center_iff] at h
      rw [Subgroup.mem_center_iff]
      intro g; apply e.injective
      calc e (g * x) = e g * e x := map_mul e g x
        _ = e x * e g := h (e g)
        _ = e (x * g) := (map_mul e x g).symm
  have hmap : (commutator G₁).map e.toMonoidHom = commutator G₂ := by
    simp only [_root_.commutator_def]
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
  let φ := QuotientGroup.liftEquiv (center G₁) hsurj hker
  let ψ := (MulEquiv.subgroupMap e (commutator G₁)).trans (MulEquiv.subgroupCongr hmap)
  exact ⟨φ, ψ, fun a₁ b₁ a₂ b₂ ha hb => by
    have ha' : QuotientGroup.mk' (center G₂) (e a₁) =
        QuotientGroup.mk' (center G₂) a₂ := ha
    have hb' : QuotientGroup.mk' (center G₂) (e b₁) =
        QuotientGroup.mk' (center G₂) b₂ := hb
    rw [QuotientGroup.mk'_eq_mk'] at ha' hb'
    obtain ⟨za, hza_mem, hza_eq⟩ := ha'
    obtain ⟨zb, hzb_mem, hzb_eq⟩ := hb'
    have hmema : (e a₁)⁻¹ * a₂ ∈ center G₂ := by
      have : (e a₁)⁻¹ * a₂ = za := by rw [← hza_eq]; group
      rw [this]; exact hza_mem
    have hmemb : (e b₁)⁻¹ * b₂ ∈ center G₂ := by
      have : (e b₁)⁻¹ * b₂ = zb := by rw [← hzb_eq]; group
      rw [this]; exact hzb_mem
    ext
    change (e ⁅a₁, b₁⁆ : G₂) = ⁅a₂, b₂⁆
    rw [map_commutatorElement]
    exact commutatorElement_center_congr hmema hmemb⟩

end Isoclinism

/-! ### Stem groups -/

/-- A group is a **stem group** if its center is contained in its derived subgroup: `Z(G) ≤ [G,G]`.
Stem groups are the smallest representatives of each isoclinism family. Every isoclinism class
contains at least one stem group. -/
def IsStemGroup (G : Type*) [Group G] : Prop :=
  center G ≤ commutator G

/-! ### Isoclinism invariants -/

section Invariants

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

/-- The cardinality of the derived subgroup is an isoclinism invariant. -/
theorem card_commutator_eq_of_isoclinism (iso : Isoclinism G₁ G₂) :
    Nat.card ↥(commutator G₁) = Nat.card ↥(commutator G₂) :=
  Nat.card_congr iso.ψ.toEquiv

/-- The cardinality of `G/Z(G)` is an isoclinism invariant. -/
theorem card_quotient_center_eq_of_isoclinism (iso : Isoclinism G₁ G₂) :
    Nat.card (G₁ ⧸ center G₁) = Nat.card (G₂ ⧸ center G₂) :=
  Nat.card_congr iso.φ.toEquiv

/-- Groups with different commutator subgroup cardinalities are not isoclinic. -/
theorem not_isoclinic_of_card_commutator_ne
    (h : Nat.card ↥(commutator G₁) ≠ Nat.card ↥(commutator G₂)) :
    Isoclinism G₁ G₂ → False :=
  fun iso => h (card_commutator_eq_of_isoclinism iso)

/-- Groups with different `|G/Z(G)|` are not isoclinic. -/
theorem not_isoclinic_of_card_quotient_center_ne
    (h : Nat.card (G₁ ⧸ center G₁) ≠ Nat.card (G₂ ⧸ center G₂)) :
    Isoclinism G₁ G₂ → False :=
  fun iso => h (card_quotient_center_eq_of_isoclinism iso)

end Invariants

end Smallgroups.UsefulTheorems
