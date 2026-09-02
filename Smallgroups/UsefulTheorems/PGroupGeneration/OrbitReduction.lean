/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleSynthesis
import Smallgroups.UsefulTheorems.PGroupGeneration.Equivalences

/-!
# Linear certificates for automorphism orbits in central cohomology

An external generator only supplies bit-packed columns for an automorphism's action on a
chosen `H²` basis and the corresponding one-cochain corrections.  The definitions below
turn a checked equality of linear maps into an isomorphism of cocycle extensions.  Thus an
orbit of `2^h` cocycles needs one check per automorphism generator and basis column, rather
than one large finite check for every vector in the orbit.
-/

namespace Smallgroups.UsefulTheorems.GF2Certificate

open scoped BigOperators

/-- Linear synthesis of an arbitrary finite `F₂` vector from bit-packed columns. -/
def synthesizeVec {k n : ℕ} (columns : Fin k → ℕ) :
    (Fin k → F2) →ₗ[F2] (Fin n → F2) where
  toFun c := fun p => ∑ i, c i * coeffMask n (columns i) p
  map_add' x y := by
    classical
    ext p
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    classical
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

namespace Order16Table

variable (T : CertifiedGroupTable 16)

/-- Decoding normalized one-cochains is linear. -/
def decodeOneLinear : OneVec →ₗ[F2] (Q T → F2) where
  toFun := decodeOne T
  map_add' x y := by
    ext a
    by_cases h : a.val = 0 <;> simp [decodeOne, h]
  map_smul' r x := by
    ext a
    by_cases h : a.val = 0 <;> simp [decodeOne, h]

/-- Decoding normalized two-cochains is linear. -/
def decodeTwoLinear : TwoVec →ₗ[F2] (Q T → Q T → F2) where
  toFun := decodeTwo T
  map_add' x y := by
    ext a b
    by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0 <;>
      simp [decodeTwo, ha, hb]
  map_smul' r x := by
    ext a b
    by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0 <;>
      simp [decodeTwo, ha, hb]

/-- Precomposition of a two-cochain by a base automorphism is linear. -/
def precomposeTwoLinear (α : Q T ≃* Q T) :
    (Q T → Q T → F2) →ₗ[F2] (Q T → Q T → F2) where
  toFun f := fun a b => f (α a) (α b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The normalized central coboundary operator on function-valued cochains is linear. -/
def centralCoboundaryLinear : (Q T → F2) →ₗ[F2] (Q T → Q T → F2) where
  toFun d := centralCoboundary (Q T) F2 d
  map_add' x y := by
    ext a b
    simp only [centralCoboundary, Pi.add_apply]
    ring
  map_smul' r x := by
    ext a b
    simp only [centralCoboundary, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The linear action on `H²` coordinates encoded by bit-packed columns. -/
def orbitAction {h : ℕ} (columns : Fin h → ℕ) :
    (Fin h → F2) →ₗ[F2] (Fin h → F2) :=
  synthesizeVec columns

/-- The correction one-cochain associated to a linear combination of `H²` columns. -/
def orbitCorrection {h : ℕ} (columns : Fin h → ℕ) :
    (Fin h → F2) →ₗ[F2] (Q T → F2) :=
  (decodeOneLinear T).comp (synthesizeOne columns)

/-- The cocycle represented by a vector of coefficients in a checked `H²` basis. -/
def hCocycle {h : ℕ} (basis : Fin h → ℕ) (c : Fin h → F2) : Q T → Q T → F2 :=
  decodeTwo T (synthesizeTwo basis c)

theorem hCocycle_consistent {h : ℕ} (basis : Fin h → ℕ)
    (hbasis : ∀ i, IsCentralCocycle (decodeTwo T (twoMask (basis i))))
    (c : Fin h → F2) : IsCentralCocycle (hCocycle T basis c) :=
  isCentralCocycle_decodeTwo_synthesize T basis hbasis c

/-- Changing a cocycle only by a proved function equality changes no group law. -/
def CocycleGroup.congrCocycleEq {Q : Type*} [Group Q] {M : Type*} [AddCommGroup M]
    {f g : Q → Q → M} (hf : IsCentralCocycle f) (hg : IsCentralCocycle g)
    (hfg : f = g) : CocycleGroup f hf ≃* CocycleGroup g hg := by
  subst g
  exact MulEquiv.refl _

/-- A checked linear-map identity for one base automorphism produces the corresponding
extension isomorphism for every `H²` coefficient vector at once. -/
noncomputable def orbitStepEquiv {h : ℕ} (basis actionColumns correctionColumns : Fin h → ℕ)
    (hbasis : ∀ i, IsCentralCocycle (decodeTwo T (twoMask (basis i))))
    (α : Q T ≃* Q T)
    (hlinear :
      (precomposeTwoLinear T α).comp ((decodeTwoLinear T).comp (synthesizeTwo basis)) =
        (centralCoboundaryLinear T).comp (orbitCorrection T correctionColumns) +
          (decodeTwoLinear T).comp
            ((synthesizeTwo basis).comp (orbitAction actionColumns)))
    (c : Fin h → F2) :
    CocycleGroup (hCocycle T basis c) (hCocycle_consistent T basis hbasis c) ≃*
      CocycleGroup (hCocycle T basis (orbitAction actionColumns c))
        (hCocycle_consistent T basis hbasis (orbitAction actionColumns c)) := by
  let f := hCocycle T basis c
  let hf := hCocycle_consistent T basis hbasis c
  let c' := orbitAction actionColumns c
  let f' := hCocycle T basis c'
  let hf' := hCocycle_consistent T basis hbasis c'
  let d := orbitCorrection T correctionColumns c
  have hd : d 1 = 0 := by
    simp [d, orbitCorrection, decodeOneLinear]
  have htransport : (fun a b => f (α a) (α b)) = addCoboundary f' d := by
    have hvalue := LinearMap.congr_fun hlinear c
    funext a b
    have hab := congrFun (congrFun hvalue a) b
    change f (α a) (α b) = f' a b + centralCoboundary (Q T) F2 d a b
    rw [add_comm]
    simpa [f, f', c', d, hCocycle, precomposeTwoLinear, decodeTwoLinear,
      centralCoboundaryLinear, orbitCorrection, addCoboundary, centralCoboundary,
      LinearMap.add_apply] using hab
  exact (CocycleGroup.congrRight hf α).symm |>.trans
    ((CocycleGroup.congrCocycleEq (hf.comp α.toMonoidHom)
      (hf'.addCoboundary d hd) htransport).trans
        (CocycleGroup.coboundaryEquiv hf' d hd))

/-- Apply a word in the generated automorphism action to `H²` coordinates. -/
def applyOrbitPath {a h : ℕ} (actionColumns : Fin a → Fin h → ℕ) :
    List (Fin a) → (Fin h → F2) → (Fin h → F2)
  | [], c => c
  | g :: word, c =>
      applyOrbitPath actionColumns word (orbitAction (actionColumns g) c)

/-- Compose the checked one-generator extension isomorphisms along an automorphism word. -/
noncomputable def orbitPathEquiv {a h : ℕ} (basis : Fin h → ℕ)
    (actionColumns correctionColumns : Fin a → Fin h → ℕ)
    (hbasis : ∀ i, IsCentralCocycle (decodeTwo T (twoMask (basis i))))
    (α : Fin a → Q T ≃* Q T)
    (hlinear : ∀ g,
      (precomposeTwoLinear T (α g)).comp
          ((decodeTwoLinear T).comp (synthesizeTwo basis)) =
        (centralCoboundaryLinear T).comp
            (orbitCorrection T (correctionColumns g)) +
          (decodeTwoLinear T).comp
            ((synthesizeTwo basis).comp (orbitAction (actionColumns g)))) :
    ∀ (word : List (Fin a)) (c : Fin h → F2),
      CocycleGroup (hCocycle T basis c) (hCocycle_consistent T basis hbasis c) ≃*
        CocycleGroup (hCocycle T basis (applyOrbitPath actionColumns word c))
          (hCocycle_consistent T basis hbasis (applyOrbitPath actionColumns word c))
  | [], _ => MulEquiv.refl _
  | g :: word, c =>
      (orbitStepEquiv T basis (actionColumns g) (correctionColumns g) hbasis
        (α g) (hlinear g) c).trans
      (orbitPathEquiv basis actionColumns correctionColumns hbasis α hlinear word
        (orbitAction (actionColumns g) c))

end Order16Table

end Smallgroups.UsefulTheorems.GF2Certificate
