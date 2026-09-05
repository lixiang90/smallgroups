/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.GAP.Polycyclic.CyclicExtension
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Polycyclic groups from pc presentations

The second ingredient of the polycyclic machinery: building a concrete finite group
from a **pc presentation** (`PCPres`), the data format used by the GAP SmallGroups
library.

* `PCLayer` — one layer of a presentation: the relative order `r` of the new pc
  generator `g`, the exponent vector `power` of `g ^ r` over the inner generators,
  and the exponent vectors `conj` of the conjugates `(inner generator) ^ g`.
  All exponent vectors are lists of natural numbers over the *inner* generators
  (normal-form exponents, `0 ≤ e < r`).
* `PCPres` — a list of layers, outermost generator first (GAP's `Pcgs` order).
* `pcBuild` — the tower construction: the group of the last `m` layers is built
  from the group of the last `m - 1` layers by a cyclic extension
  (`Polycyclic/CyclicExtension.lean`).  The layer datum `pcLayerData` is
  proof-free; the conjugation function is the letter-by-letter map
  `h ↦ evalVec (coords h) (images of the generators)`.
* `PCGroup p` — the group of a presentation, with computable `Mul`/`One`/`Inv`/
  `Fintype`/`DecidableEq` instances.  The `Group` instance is available once the
  presentation is proved consistent (`pcConsistent p.layers`, decidable:
  `PCGroup.groupOfConsistent p (by decide)`).
* `pcTuple` — the normal-form bijection
  `pcTower ds ≃ ∀ i : Fin ds.length, ZMod (ds[i].r)`,
  and `card_PCGroup : Nat.card (PCGroup p) = ∏ rᵢ`.
* `mulEquivOfDecide` — build a `MulEquiv` from a function whose homomorphism
  property and bijectivity are discharged by `decide`; used to identify imported
  pc groups with the project's existing representatives.
-/

namespace Smallgroups.GAP

variable {G : Type*}

/-- Raw natural power, needing only `Mul` and `One` (no algebraic laws). -/
def rpow [Mul G] [One G] (x : G) : ℕ → G
  | 0 => 1
  | (n + 1) => rpow x n * x

/-- `rpow` agrees with the monoid power. -/
theorem rpow_eq_npow [Monoid G] (x : G) : ∀ n : ℕ, rpow x n = x ^ n
  | 0 => (pow_zero x).symm
  | n + 1 => by rw [rpow, rpow_eq_npow x n, pow_succ]

/-- Interpret an exponent vector over a list of generators:
`evalVec [e₁, …, eₖ] [g₁, …, gₙ] = g₁^{e₁} ⋯ gₖ^{eₖ}` (short vectors are ignored
past their length). -/
def evalVec [Mul G] [One G] (v : List ℕ) (gs : List G) : G :=
  (v.zipWith (fun e g => rpow g e) gs).prod

/-! ## The data of a pc presentation -/

/-- One layer of a pc presentation (mirrors the GAP data): the relative order `r`
of the new pc generator `g`, the exponent vector of `g ^ r` over the inner
generators, and the exponent vectors of the conjugates `(inner generator) ^ g`. -/
structure PCLayer where
  /-- The relative order of the new generator. -/
  r : ℕ
  /-- The relative order is positive. -/
  hr : 0 < r
  /-- The exponent vector of `g ^ r` over the inner generators. -/
  power : List ℕ
  /-- `conj[k]` is the exponent vector of `(inner generator k) ^ g`. -/
  conj : List (List ℕ)

/-- A pc presentation: the list of layers, outermost generator first
(GAP's `Pcgs` order). -/
structure PCPres where
  /-- The layers, outermost generator first. -/
  layers : List PCLayer

/-! ## The tower construction -/

/-- The bundle produced by the tower construction: the carrier type together with
its raw operations, the normal-form coordinate function, and the pc generators. -/
structure TowerPack where
  /-- The carrier type. -/
  T : Type
  /-- The raw multiplication. -/
  mul : Mul T
  /-- The raw one. -/
  one : One T
  /-- The raw inversion. -/
  inv : Inv T
  /-- The normal-form coordinates of an element. -/
  coords : T → List ℕ
  /-- The pc generators, outermost first. -/
  gens : List T

/-- The cyclic extension data for one layer over a group `T` with coordinate
function `coords` and pc generators `gens`.  The conjugation function is the
letter-by-letter map `h ↦ ∏ (images)ₖ ^ (coords h)ₖ` — evaluated innermost-first,
matching the tower's normal form (hence the `reverse`s). -/
def pcLayerData (L : PCLayer) {T : Type} [Mul T] [One T] (coords : T → List ℕ)
    (gens : List T) : CycExtData T :=
  ⟨L.r, fun h => evalVec ((coords h).reverse)
      (L.conj.map (fun v => evalVec v gens)).reverse,
    evalVec L.power gens, L.hr⟩

/-- The tower construction: `pcBuild ds` is the group of the layers of `ds`,
built from the inside out by cyclic extensions. -/
@[reducible]
def pcBuild : List PCLayer → TowerPack
  | [] => ⟨PUnit, inferInstance, inferInstance, inferInstance, fun _ => [], []⟩
  | L :: rest =>
      let pack := pcBuild rest
      letI : Mul pack.T := pack.mul
      letI : One pack.T := pack.one
      letI : Inv pack.T := pack.inv
      let D := pcLayerData L pack.coords pack.gens
      ⟨CycExt D, CycExt.instMul D, CycExt.instOne D, CycExt.instInv D,
        fun h => h.snd.val :: pack.coords h.fst,
        CycExt.gen D :: pack.gens.map (CycExt.inlFn D)⟩

/-- The carrier type of the tower. -/
@[reducible]
def pcTower (ds : List PCLayer) : Type := (pcBuild ds).T

/-- The layer datum used at each step of the tower. -/
@[reducible]
def pcTowerLayerData (L : PCLayer) (rest : List PCLayer) : CycExtData (pcTower rest) :=
  let pack := pcBuild rest
  letI : Mul pack.T := pack.mul
  letI : One pack.T := pack.one
  (pcLayerData L pack.coords pack.gens : CycExtData pack.T)

/-- The pc generators of the tower, outermost first. -/
def pcGens (ds : List PCLayer) : List (pcTower ds) := (pcBuild ds).gens

/-- The normal-form coordinates of an element of the tower. -/
def pcCoords (ds : List PCLayer) : pcTower ds → List ℕ := (pcBuild ds).coords

/-- Map out of a tower by specifying the images of the pc generators:
`x ↦ imgsₙ ^ (coords x)ₙ ⋯ imgs₁ ^ (coords x)₁` (the tower's normal form is
innermost-first, hence the reversal).  For the correct images (the normal-form word
of each pc generator in the target) this is a homomorphism, checkable by `decide`
(`mulEquivOfDecide`). -/
def pcEval (ds : List PCLayer) {H : Type*} [Mul H] [One H] (imgs : List H) :
    pcTower ds → H :=
  fun x => evalVec ((pcCoords ds x).reverse) imgs.reverse

/-- Decidable equality on the tower. -/
@[reducible]
def pcGroupDecEq : (ds : List PCLayer) → DecidableEq (pcTower ds)
  | [] => (inferInstance : DecidableEq PUnit)
  | L :: rest =>
      letI := pcGroupDecEq rest
      CycExt.instDecidableEq (pcTowerLayerData L rest)

/-- The tower is finite. -/
@[reducible]
def pcGroupFintype : (ds : List PCLayer) → Fintype (pcTower ds)
  | [] => (inferInstance : Fintype PUnit)
  | L :: rest =>
      letI := pcGroupFintype rest
      letI := pcGroupDecEq rest
      CycExt.instFintype (pcTowerLayerData L rest)

/-- Consistency of a whole presentation: every layer datum is consistent. -/
def pcConsistent : (ds : List PCLayer) → Prop
  | [] => True
  | L :: rest =>
      let pack := pcBuild rest
      @CycExtData.Consistent _ pack.mul pack.one pack.inv (pcTowerLayerData L rest) ∧
        pcConsistent rest

/-- Consistency of a presentation is decidable. -/
instance pcConsistentDecidable : (ds : List PCLayer) → Decidable (pcConsistent ds)
  | [] => (inferInstance : Decidable True)
  | L :: rest =>
      let pack := pcBuild rest
      @instDecidableAnd _ _
        (@CycExtData.decidableConsistent _ pack.mul pack.one pack.inv
          (pcGroupFintype rest) (pcGroupDecEq rest) (pcTowerLayerData L rest))
        (pcConsistentDecidable rest)

/-- The group of a pc presentation. -/
@[reducible]
def PCGroup (p : PCPres) : Type := pcTower p.layers

instance (p : PCPres) : Mul (PCGroup p) := (pcBuild p.layers).mul

instance (p : PCPres) : One (PCGroup p) := (pcBuild p.layers).one

instance (p : PCPres) : Inv (PCGroup p) := (pcBuild p.layers).inv

instance (p : PCPres) : Fintype (PCGroup p) := pcGroupFintype p.layers

instance (p : PCPres) : DecidableEq (PCGroup p) := pcGroupDecEq p.layers

/-- The normal-form bijection: elements of the tower correspond to tuples of
exponents. -/
def pcTuple : (ds : List PCLayer) → pcTower ds ≃ ∀ i : Fin ds.length, ZMod (ds[i.1].r)
  | [] =>
      ⟨fun _ => fun i => i.elim0, fun _ => PUnit.unit,
        fun x => by cases x; rfl,
        fun f => funext fun i => i.elim0⟩
  | L :: rest =>
      (CycExt.toProd _).trans ((Equiv.prodComm _ _).trans
        (((Equiv.refl _).prodCongr (pcTuple rest)).trans
          (Fin.consEquiv (fun i : Fin (rest.length + 1) => ZMod ((L :: rest)[i.1].r)))))

/-- The normal-form bijection for a presentation's group. -/
def PCGroup.tupleEquiv (p : PCPres) :
    PCGroup p ≃ ∀ i : Fin p.layers.length, ZMod (p.layers[i.1].r) :=
  pcTuple p.layers

/-- The order of the tower is the product of the relative orders. -/
theorem card_PCGroup (p : PCPres) :
    Nat.card (PCGroup p) = (p.layers.map PCLayer.r).prod := by
  obtain ⟨ds⟩ := p
  induction ds with
  | nil => simp [PCGroup, pcTower]
  | cons L rest ih =>
      haveI : Finite (pcTower rest) := Fintype.finite (pcGroupFintype rest)
      rw [List.map_cons, List.prod_cons, ← ih]
      exact CycExt.card_cycExt (D := pcTowerLayerData L rest)

/-! ## Building isomorphisms by `decide` -/

/-- Build a multiplicative equivalence from a function whose homomorphism property
and bijectivity are decidable (default: `by decide`).  Used to identify imported
pc groups with the project's existing representatives. -/
noncomputable def mulEquivOfDecide {G H : Type*} [Group G] [Group H] [Fintype G]
    [DecidableEq G] [Fintype H] [DecidableEq H] (f : G → H)
    (hmul : ∀ x y, f (x * y) = f x * f y := by decide)
    (hbij : Function.Bijective f := by decide) : G ≃* H :=
  MulEquiv.ofBijective (MonoidHom.mk' f hmul) hbij

end Smallgroups.GAP
