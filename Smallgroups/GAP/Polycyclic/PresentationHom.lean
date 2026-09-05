/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.Basic

/-!
# Homomorphisms out of polycyclic presentations

This file constructs a homomorphism out of one cyclic-extension layer from the image
of the inner group and the image of the new generator.  The required hypotheses are
exactly the power and conjugation relations of that layer.  It is the induction step
for relation-based maps out of a full pc tower.
-/

namespace Smallgroups.GAP
namespace CycExt

variable {G H : Type*} [Group G] [Group H] {D : CycExtData G} [D.Consistent]

/-- A concrete list of generators, together with its mathematical generation proof.
For a pc tower, the instances below produce the same recursively constructed list as
`pcGens`, without enumerating any of the elements of the tower. -/
class GeneratingList (G : Type*) [Group G] where
  elems : List G
  generates : Subgroup.closure {g | g ∈ elems} = ⊤

/-- The list carried by a `GeneratingList` instance. -/
def generatingList (G : Type*) [Group G] [GeneratingList G] : List G :=
  GeneratingList.elems

instance generatingListPUnit : GeneratingList PUnit where
  elems := []
  generates := by
    apply top_unique
    intro x _
    have hx : x = 1 := Subsingleton.elim _ _
    simpa only [hx] using (Subgroup.one_mem (Subgroup.closure {g : PUnit | g ∈ []}))

/-- The new cyclic generator and an embedded generating list generate an extension.
This is the only induction step needed to obtain generators of every pc tower. -/
instance generatingListCycExt [GeneratingList G] : GeneratingList (CycExt D) where
  elems := gen D :: (generatingList G).map (inlFn D)
  generates := by
    let S : Subgroup (CycExt D) :=
      Subgroup.closure {x | x ∈ gen D :: (generatingList G).map (inlFn D)}
    have hinner : ∀ g : G, inl D g ∈ S := by
      have hle : Subgroup.closure {g | g ∈ generatingList G} ≤ S.comap (inl D) := by
        apply (Subgroup.closure_le _).2
        intro g hg
        apply Subgroup.subset_closure
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
      rw [show Subgroup.closure {g | g ∈ generatingList G} = ⊤ from
        GeneratingList.generates] at hle
      exact fun g => hle (by trivial)
    have hgen : gen D ∈ S := Subgroup.subset_closure (by simp)
    apply top_unique
    intro x _
    rw [eq_inl_mul_gen_pow D x]
    exact S.mul_mem (hinner x.fst) (S.pow_mem hgen _)

/-- Conjugation compatibility only has to be checked on a generating list: both
sides define homomorphisms, so agreement extends to the entire generated subgroup. -/
theorem conjugation_of_generator_relations [GeneratingList G] (φ : G →* H) (t : H)
    (hconj : ∀ i : Fin (generatingList G).length,
      t * φ ((generatingList G).get i) * t⁻¹ =
        φ (D.f ((generatingList G).get i))) :
    ∀ g, t * φ g * t⁻¹ = φ (D.f g) := by
  let left : G →* H :=
    { toFun := fun g => t * φ g * t⁻¹
      map_one' := by simp
      map_mul' := by intro a b; simp only [map_mul]; group }
  let action : G →* G :=
    { toFun := D.f
      map_one' := CycExtData.Consistent.one
      map_mul' := CycExtData.Consistent.hom }
  have hpoint : ∀ g ∈ generatingList G, t * φ g * t⁻¹ = φ (D.f g) :=
    List.forall_mem_iff_get.mpr hconj
  have heq : left = φ.comp action :=
    MonoidHom.eq_of_eqOn_dense GeneratingList.generates (by
      intro g hg
      exact hpoint g hg)
  intro g
  exact DFunLike.congr_fun heq g

/-- Turn a homomorphism with an explicit right inverse into an isomorphism when the
finite source and target have the same cardinality.  Only the right-inverse equation
is computationally checked by clients. -/
noncomputable def mulEquivOfRightInverseCardEq {A B : Type*} [Group A] [Group B]
    [Fintype A] [Fintype B] (φ : A →* B) (g : B → A)
    (hright : Function.RightInverse g φ)
    (hcard : Nat.card A = Nat.card B) : A ≃* B :=
  MulEquiv.ofBijective φ ((Fintype.bijective_iff_surjective_and_card φ).2
    ⟨hright.surjective, by simpa only [← Nat.card_eq_fintype_card] using hcard⟩)

/-- Build a multiplicative equivalence from explicit forward and inverse functions.
This is useful when both groups have cheap normal-form indices: clients check the
multiplication law and the two inverse laws, without enumerating a generic bijectivity
predicate. -/
noncomputable def mulEquivOfExplicitInverse {A B : Type*} [Group A] [Group B]
    (f : A → B) (g : B → A) (hmul : ∀ x y, f (x * y) = f x * f y)
    (hinv : Function.LeftInverse g f ∧ Function.RightInverse g f) : A ≃* B where
  toFun := f
  invFun := g
  left_inv := hinv.1
  right_inv := hinv.2
  map_mul' := hmul

omit [D.Consistent] in
private theorem pow_mul_map_iterate (φ : G →* H) (t : H)
    (hconj : ∀ g, t * φ g * t⁻¹ = φ (D.f g)) :
    ∀ (n : ℕ) (g : G), t ^ n * φ g = φ (D.f^[n] g) * t ^ n := by
  have hstep (g : G) : t * φ g = φ (D.f g) * t := by
    calc
      t * φ g = (t * φ g * t⁻¹) * t := by group
      _ = φ (D.f g) * t := by rw [hconj]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro g
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, hstep, mul_assoc,
        ← pow_succ', Function.iterate_succ_apply']

omit [D.Consistent] in
private theorem pow_add_mod (φ : G →* H) (t : H)
    (hpow : t ^ D.r = φ D.a) (i j : ZMod D.r) :
    t ^ i.val * t ^ j.val = φ (D.coc i j) * t ^ (i + j).val := by
  rw [← pow_add]
  by_cases h : i.val + j.val < D.r
  · rw [ZMod.val_add_of_lt h]
    simp [CycExtData.coc, h]
  · have hv := ZMod.val_add_of_le (le_of_not_gt h)
    rw [CycExtData.coc, if_neg h]
    have hsum : i.val + j.val = (i + j).val + D.r := by omega
    rw [hsum, pow_add, hpow, ← hpow, ← pow_add, ← pow_add, Nat.add_comm]

/-- Map a cyclic extension into a target group by mapping the inner group with `φ`
and the new generator to `t`.  The proof checks only the layer's power relation and
its conjugation action; multiplication of every pair in the extension is then a
theorem rather than an exhaustive finite computation. -/
def lift (φ : G →* H) (t : H) (hpow : t ^ D.r = φ D.a)
    (hconj : ∀ g, t * φ g * t⁻¹ = φ (D.f g)) : CycExt D →* H where
  toFun x := φ x.fst * t ^ x.snd.val
  map_one' := by simp
  map_mul' x y := by
    change φ (x.fst * D.f^[x.snd.val] y.fst * D.coc x.snd y.snd) *
        t ^ (x.snd + y.snd).val =
      (φ x.fst * t ^ x.snd.val) * (φ y.fst * t ^ y.snd.val)
    symm
    calc
      (φ x.fst * t ^ x.snd.val) * (φ y.fst * t ^ y.snd.val) =
          φ x.fst * (t ^ x.snd.val * φ y.fst) * t ^ y.snd.val := by group
      _ = φ x.fst * (φ (D.f^[x.snd.val] y.fst) * t ^ x.snd.val) *
          t ^ y.snd.val := by rw [pow_mul_map_iterate φ t hconj]
      _ = φ x.fst * φ (D.f^[x.snd.val] y.fst) *
          (t ^ x.snd.val * t ^ y.snd.val) := by group
      _ = φ x.fst * φ (D.f^[x.snd.val] y.fst) *
          (φ (D.coc x.snd y.snd) * t ^ (x.snd + y.snd).val) := by
            rw [pow_add_mod φ t hpow]
      _ = φ (x.fst * D.f^[x.snd.val] y.fst * D.coc x.snd y.snd) *
          t ^ (x.snd + y.snd).val := by rw [map_mul, map_mul]; group

/-- The same constructor with the power and conjugation relations packaged as one
finite proposition.  Generated certificates can kernel-reduce this conjunction in a
single `decide` invocation. -/
def liftOfRelations (φ : G →* H) (t : H)
    (hrel : t ^ D.r = φ D.a ∧ ∀ g, t * φ g * t⁻¹ = φ (D.f g)) : CycExt D →* H :=
  lift φ t hrel.1 hrel.2

/-- Construct a map out of a cyclic extension by checking its power relation and
the conjugation relations only on the inner generators.  A five-layer binary pc
tower therefore requires five power and ten generator-conjugation equalities. -/
def liftOfGeneratorRelations [GeneratingList G] (φ : G →* H) (t : H)
    (hrel : t ^ D.r = φ D.a ∧ ∀ i : Fin (generatingList G).length,
      t * φ ((generatingList G).get i) * t⁻¹ =
        φ (D.f ((generatingList G).get i))) : CycExt D →* H :=
  lift φ t hrel.1 (conjugation_of_generator_relations φ t hrel.2)

@[simp] theorem lift_inl (φ : G →* H) (t : H) (hpow) (hconj) (g : G) :
    lift φ t hpow hconj (inl D g) = φ g := by
  simp [lift, inl]

@[simp] theorem lift_gen (φ : G →* H) (t : H) (hpow) (hconj) (hr : 2 ≤ D.r) :
    lift φ t hpow hconj (gen D) = t := by
  haveI : Fact (1 < D.r) := ⟨hr⟩
  simp [lift, gen, ZMod.val_one]

end CycExt
end Smallgroups.GAP
