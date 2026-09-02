/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageParent14OrbitData
import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleSynthesis
import Smallgroups.UsefulTheorems.PGroupGeneration.Equivalences

/-! Turning one checked parent-14 orbit witness into an extension isomorphism. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

set_option maxHeartbeats 8000000 in
-- Finite verification that the ten generated `H²` basis columns are cocycles.
theorem parent14_hbasis_cocycle (i : Fin 10) :
    IsCentralCocycle
      (Order16Table.decodeTwo parent14Table (twoMask (parent14HBasis i))) := by
  fin_cases i <;> decide +kernel

def parent14OrbitCocycle (k : Fin 1024) :=
  Order16Table.decodeTwo parent14Table (parent14OrbitVec k)

theorem parent14OrbitCocycle_consistent (k : Fin 1024) :
    IsCentralCocycle (parent14OrbitCocycle k) := by
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent14Table parent14HBasis
    parent14_hbasis_cocycle (coeffMask 10 k.val)

def parent14OrbitRepresentativeCocycle (k : Fin 1024) :=
  Order16Table.decodeTwo parent14Table
    (parent14OrbitRepresentativeVec (parent14OrbitIndex k))

theorem parent14OrbitRepresentativeCocycle_consistent (k : Fin 1024) :
    IsCentralCocycle (parent14OrbitRepresentativeCocycle k) := by
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent14Table parent14HBasis
    parent14_hbasis_cocycle
    (coeffMask 10 (parent14OrbitRepresentativeMask (parent14OrbitIndex k)))

def parent14SelectedCocycle (o : Fin 7) :=
  Order16Table.decodeTwo parent14Table (parent14OrbitRepresentativeVec o)

theorem parent14SelectedCocycle_consistent (o : Fin 7) :
    IsCentralCocycle (parent14SelectedCocycle o) := by
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent14Table parent14HBasis
    parent14_hbasis_cocycle
    (coeffMask 10 (parent14OrbitRepresentativeMask o))

set_option maxHeartbeats 8000000 in
-- Exhaustive finite round-trip check for the ten-bit coefficient encoding.
theorem parent14_coeffMask_vecIndex : ∀ (c : Fin 10 → F2) (i : Fin 10),
    coeffMask 10 (vecIndex 10 c).val i = c i := by
  decide +kernel

/-- The table permutation contained in a checked orbit certificate is a group
automorphism of the parent. -/
def parent14OrbitAut (k : Fin 1024) (hc : parent14OrbitCertificate k) :
    Order16Table.Q parent14Table ≃* Order16Table.Q parent14Table where
  toFun x := ⟨parent14OrbitPerm k x.val⟩
  invFun x := ⟨parent14OrbitInvPerm k x.val⟩
  left_inv x := by
    apply CertifiedTableGroup.ext
    exact hc.1 x.val
  right_inv x := by
    apply CertifiedTableGroup.ext
    exact hc.2.1 x.val
  map_mul' x y := by
    apply CertifiedTableGroup.ext
    exact hc.2.2.1 x.val y.val

/-- Change only the definitional presentation of a cocycle; the proof fields are
irrelevant and the underlying group law is unchanged after substitution. -/
def CocycleGroup.congrCocycle {Q : Type*} [Group Q] {M : Type*} [AddCommGroup M]
    {f g : Q → Q → M} (hf : IsCentralCocycle f) (hg : IsCentralCocycle g)
    (hfg : f = g) : CocycleGroup f hf ≃* CocycleGroup g hg := by
  subst g
  exact MulEquiv.refl _

/-- A checked orbit witness gives an explicit group isomorphism from the extension at
the indexed `H²` coordinate to the extension at its chosen orbit representative. -/
noncomputable def parent14OrbitEquiv (k : Fin 1024) (hc : parent14OrbitCertificate k) :
    CocycleGroup (parent14OrbitCocycle k) (parent14OrbitCocycle_consistent k) ≃*
      CocycleGroup (parent14OrbitRepresentativeCocycle k)
        (parent14OrbitRepresentativeCocycle_consistent k) := by
  let f := parent14OrbitCocycle k
  let hf := parent14OrbitCocycle_consistent k
  let d := Order16Table.decodeOne parent14Table (parent14OrbitOneVec k)
  have hd : d 1 = 0 := Order16Table.decodeOne_zero parent14Table _
  let shifted := addCoboundary f d
  let hs := hf.addCoboundary d hd
  let α := (parent14OrbitAut k hc).symm
  have hnorm : (fun a b => shifted (α a) (α b)) =
      parent14OrbitRepresentativeCocycle k := by
    funext a b
    symm
    simpa [shifted, f, d, α, parent14OrbitAut, parent14OrbitCocycle,
      parent14OrbitRepresentativeCocycle, addCoboundary, centralCoboundary] using
        hc.2.2.2 a b
  exact ((CocycleGroup.coboundaryEquiv hf d hd).symm.trans
    (CocycleGroup.congrRight hs α).symm).trans
      (CocycleGroup.congrCocycle (hs.comp α.toMonoidHom)
        (parent14OrbitRepresentativeCocycle_consistent k) hnorm)

end Smallgroups.UsefulTheorems.Order32Certificate
