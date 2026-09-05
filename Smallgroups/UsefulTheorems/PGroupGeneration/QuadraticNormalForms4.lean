/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.PGroupGeneration.QuadraticSmallDimension

/-! The seven standard quadratic forms on a four-dimensional space over `F₂`. -/

namespace Smallgroups.UsefulTheorems.GF2Certificate

/-- Standard forms in the order: zero, one square, `H`, `A`, `H` plus one square,
two hyperbolic planes, and one hyperbolic plus one anisotropic plane. -/
def quadraticFourNormalForm :
    Fin 7 → QuadraticMap F2 (QuadraticPlaneV × QuadraticPlaneV) F2 :=
  ![(0 : QuadraticMap F2 QuadraticPlaneV F2).prod 0,
    singleSquarePlane.prod 0,
    hyperbolicPlane.prod 0,
    anisotropicPlane.prod 0,
    hyperbolicPlane.prod singleSquarePlane,
    hyperbolicPlane.prod hyperbolicPlane,
    hyperbolicPlane.prod anisotropicPlane]

end Smallgroups.UsefulTheorems.GF2Certificate
