/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP14SelectedCocycle (o : Fin 7) :=
  Order16Table.hCocycle parent14Table parent14HBasis
    (coeffMask 10 (orbitP14RepresentativeMask o))

theorem orbitP14SelectedCocycle_consistent (o : Fin 7) :
    IsCentralCocycle (orbitP14SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent14Table parent14HBasis
    orbitP14_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
