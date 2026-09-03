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

theorem applyOrbitPath_append {a h : ℕ} (actionColumns : Fin a → Fin h → ℕ)
    (left right : List (Fin a)) (c : Fin h → F2) :
    applyOrbitPath actionColumns (left ++ right) c =
      applyOrbitPath actionColumns right (applyOrbitPath actionColumns left c) := by
  induction left generalizing c with
  | nil => rfl
  | cons g word ih =>
      simp only [List.cons_append, applyOrbitPath]
      exact ih (orbitAction (actionColumns g) c)

/-- Recover the generator word from a ranked orbit forest.  Roots have rank zero;
every other vertex stores its predecessor and the final generator on its path. -/
def orbitForestPathAux {a n : ℕ} (parent : Fin n → Fin n)
    (generator : Fin n → Fin a) : ℕ → Fin n → List (Fin a)
  | 0, _ => []
  | d + 1, k => orbitForestPathAux parent generator d (parent k) ++ [generator k]

/-- The generator word assigned to a vertex by a ranked orbit forest. -/
def orbitForestPath {a n : ℕ} (parent : Fin n → Fin n)
    (generator : Fin n → Fin a) (rank : Fin n → ℕ) (k : Fin n) : List (Fin a) :=
  orbitForestPathAux parent generator (rank k) k

/-- The local check attached to one vertex of a ranked orbit forest. -/
def OrbitForestEdge {a h n : ℕ} (actionColumns : Fin a → Fin h → ℕ)
    (start target : Fin n → Fin h → F2) (parent : Fin n → Fin n)
    (generator : Fin n → Fin a) (rank : Fin n → ℕ) (k : Fin n) : Prop :=
  (rank k = 0 → start k = target k) ∧
    (0 < rank k →
      rank (parent k) + 1 = rank k ∧
        start (parent k) = start k ∧
          orbitAction (actionColumns (generator k)) (target (parent k)) = target k)

/-- Local checks sufficient to certify all endpoints of a ranked orbit forest.
The root clause identifies the representative coefficient vector.  The non-root
clause checks decreasing rank, a common representative, and one generator edge. -/
def OrbitForestCertificate {a h n : ℕ} (actionColumns : Fin a → Fin h → ℕ)
    (start target : Fin n → Fin h → F2) (parent : Fin n → Fin n)
    (generator : Fin n → Fin a) (rank : Fin n → ℕ) : Prop :=
  ∀ k, OrbitForestEdge actionColumns start target parent generator rank k

private theorem applyOrbitForestPathAux_eq {a h n : ℕ}
    (actionColumns : Fin a → Fin h → ℕ) (start target : Fin n → Fin h → F2)
    (parent : Fin n → Fin n) (generator : Fin n → Fin a) (rank : Fin n → ℕ)
    (certificate : OrbitForestCertificate actionColumns start target parent generator rank) :
    ∀ d k, rank k = d →
      applyOrbitPath actionColumns (orbitForestPathAux parent generator d k) (start k) =
        target k := by
  intro d
  induction d with
  | zero =>
      intro k hk
      simpa [orbitForestPathAux, applyOrbitPath] using (certificate k).1 hk
  | succ d ih =>
      intro k hk
      have hkpos : 0 < rank k := by
        rw [hk]
        exact Nat.zero_lt_succ d
      obtain ⟨hparentRank, hstart, hedge⟩ := (certificate k).2 hkpos
      have hparent : rank (parent k) = d := by
        apply Nat.succ.inj
        simpa [Nat.succ_eq_add_one, hk] using hparentRank
      rw [orbitForestPathAux, applyOrbitPath_append]
      change orbitAction (actionColumns (generator k))
          (applyOrbitPath actionColumns
            (orbitForestPathAux parent generator d (parent k)) (start k)) = target k
      rw [← hstart, ih (parent k) hparent]
      exact hedge

/-- Every path reconstructed from a locally checked ranked orbit forest reaches its
declared target.  This replaces one full path reduction per vector by one edge check. -/
theorem applyOrbitForestPath_eq {a h n : ℕ} (actionColumns : Fin a → Fin h → ℕ)
    (start target : Fin n → Fin h → F2) (parent : Fin n → Fin n)
    (generator : Fin n → Fin a) (rank : Fin n → ℕ)
    (certificate : OrbitForestCertificate actionColumns start target parent generator rank)
    (k : Fin n) :
    applyOrbitPath actionColumns (orbitForestPath parent generator rank k) (start k) =
      target k := by
  exact applyOrbitForestPathAux_eq actionColumns start target parent generator rank
    certificate (rank k) k rfl

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
