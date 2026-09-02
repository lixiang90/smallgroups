/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent01Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent02Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent03Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent04Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent05Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent06Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent07Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent08Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent09Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent10Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent11Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent12Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent13Complete
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Complete

/-! End-to-end cocycle coverage for all order-16 parent tables. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate
open Smallgroups.GAP

theorem order16ParentTable_cocycle_gap_complete : ∀ (p : Fin 14)
    (f : Order16Table.Q (order16ParentTable p) →
      Order16Table.Q (order16ParentTable p) → F2)
    (hf : IsCentralCocycle f),
    ∃ j : Fin 51, Nonempty (CocycleGroup f hf ≃* smallGroup32 j)
  | 0, f, hf => orbitP1_cocycle_gap_complete f hf
  | 1, f, hf => orbitP2_cocycle_gap_complete f hf
  | 2, f, hf => orbitP3_cocycle_gap_complete f hf
  | 3, f, hf => orbitP4_cocycle_gap_complete f hf
  | 4, f, hf => orbitP5_cocycle_gap_complete f hf
  | 5, f, hf => orbitP6_cocycle_gap_complete f hf
  | 6, f, hf => orbitP7_cocycle_gap_complete f hf
  | 7, f, hf => orbitP8_cocycle_gap_complete f hf
  | 8, f, hf => orbitP9_cocycle_gap_complete f hf
  | 9, f, hf => orbitP10_cocycle_gap_complete f hf
  | 10, f, hf => orbitP11_cocycle_gap_complete f hf
  | 11, f, hf => orbitP12_cocycle_gap_complete f hf
  | 12, f, hf => orbitP13_cocycle_gap_complete f hf
  | 13, f, hf => orbitP14_cocycle_gap_complete f hf

end Smallgroups.UsefulTheorems.Order32Certificate
