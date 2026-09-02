/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Core
import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14PathPart44

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Checked short orbit paths for parent 14; generated part 45. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

theorem orbitP14_path_endpoint_704 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 1, 2, 1, 0, 1]
      (orbitP14RepresentativeCoeff 704) = orbitP14TargetCoeff 704 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv704 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 704))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 704)) ≃*
      CocycleGroup (orbitP14TargetCocycle 704)
        (orbitP14TargetCocycle_consistent 704) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 1, 2, 1, 0, 1] (orbitP14RepresentativeCoeff 704)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_704))

theorem orbitP14_path_endpoint_705 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2]
      (orbitP14RepresentativeCoeff 705) = orbitP14TargetCoeff 705 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv705 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 705))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 705)) ≃*
      CocycleGroup (orbitP14TargetCocycle 705)
        (orbitP14TargetCocycle_consistent 705) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2] (orbitP14RepresentativeCoeff 705)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_705))

theorem orbitP14_path_endpoint_706 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 706) = orbitP14TargetCoeff 706 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv706 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 706))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 706)) ≃*
      CocycleGroup (orbitP14TargetCocycle 706)
        (orbitP14TargetCocycle_consistent 706) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 706)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_706))

theorem orbitP14_path_endpoint_707 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 2, 0, 1, 2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 707) = orbitP14TargetCoeff 707 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv707 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 707))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 707)) ≃*
      CocycleGroup (orbitP14TargetCocycle 707)
        (orbitP14TargetCocycle_consistent 707) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 2, 0, 1, 2, 1, 2, 1] (orbitP14RepresentativeCoeff 707)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_707))

theorem orbitP14_path_endpoint_708 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 1, 2, 1, 1, 2]
      (orbitP14RepresentativeCoeff 708) = orbitP14TargetCoeff 708 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv708 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 708))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 708)) ≃*
      CocycleGroup (orbitP14TargetCocycle 708)
        (orbitP14TargetCocycle_consistent 708) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 1, 2, 1, 1, 2] (orbitP14RepresentativeCoeff 708)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_708))

theorem orbitP14_path_endpoint_709 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 709) = orbitP14TargetCoeff 709 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv709 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 709))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 709)) ≃*
      CocycleGroup (orbitP14TargetCocycle 709)
        (orbitP14TargetCocycle_consistent 709) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 709)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_709))

theorem orbitP14_path_endpoint_710 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 1, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 710) = orbitP14TargetCoeff 710 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv710 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 710))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 710)) ≃*
      CocycleGroup (orbitP14TargetCocycle 710)
        (orbitP14TargetCocycle_consistent 710) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 1, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 710)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_710))

theorem orbitP14_path_endpoint_711 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 0, 2, 1, 1, 2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 711) = orbitP14TargetCoeff 711 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv711 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 711))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 711)) ≃*
      CocycleGroup (orbitP14TargetCocycle 711)
        (orbitP14TargetCocycle_consistent 711) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 0, 2, 1, 1, 2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 711)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_711))

theorem orbitP14_path_endpoint_712 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0]
      (orbitP14RepresentativeCoeff 712) = orbitP14TargetCoeff 712 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv712 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 712))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 712)) ≃*
      CocycleGroup (orbitP14TargetCocycle 712)
        (orbitP14TargetCocycle_consistent 712) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0] (orbitP14RepresentativeCoeff 712)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_712))

theorem orbitP14_path_endpoint_713 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 2, 0, 1, 2, 1]
      (orbitP14RepresentativeCoeff 713) = orbitP14TargetCoeff 713 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv713 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 713))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 713)) ≃*
      CocycleGroup (orbitP14TargetCocycle 713)
        (orbitP14TargetCocycle_consistent 713) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 2, 0, 1, 2, 1] (orbitP14RepresentativeCoeff 713)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_713))

theorem orbitP14_path_endpoint_714 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [0, 2, 0, 1, 0, 1, 2]
      (orbitP14RepresentativeCoeff 714) = orbitP14TargetCoeff 714 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv714 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 714))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 714)) ≃*
      CocycleGroup (orbitP14TargetCocycle 714)
        (orbitP14TargetCocycle_consistent 714) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [0, 2, 0, 1, 0, 1, 2] (orbitP14RepresentativeCoeff 714)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_714))

theorem orbitP14_path_endpoint_715 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 2, 1]
      (orbitP14RepresentativeCoeff 715) = orbitP14TargetCoeff 715 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv715 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 715))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 715)) ≃*
      CocycleGroup (orbitP14TargetCocycle 715)
        (orbitP14TargetCocycle_consistent 715) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 2, 1] (orbitP14RepresentativeCoeff 715)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_715))

theorem orbitP14_path_endpoint_716 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [1, 2, 0, 1, 0, 2, 1, 1, 0, 2]
      (orbitP14RepresentativeCoeff 716) = orbitP14TargetCoeff 716 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv716 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 716))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 716)) ≃*
      CocycleGroup (orbitP14TargetCocycle 716)
        (orbitP14TargetCocycle_consistent 716) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [1, 2, 0, 1, 0, 2, 1, 1, 0, 2] (orbitP14RepresentativeCoeff 716)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_716))

theorem orbitP14_path_endpoint_717 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 0, 1, 0, 2]
      (orbitP14RepresentativeCoeff 717) = orbitP14TargetCoeff 717 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv717 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 717))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 717)) ≃*
      CocycleGroup (orbitP14TargetCocycle 717)
        (orbitP14TargetCocycle_consistent 717) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 0, 1, 0, 2] (orbitP14RepresentativeCoeff 717)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_717))

theorem orbitP14_path_endpoint_718 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 1, 0, 2, 1, 1, 1, 2]
      (orbitP14RepresentativeCoeff 718) = orbitP14TargetCoeff 718 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv718 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 718))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 718)) ≃*
      CocycleGroup (orbitP14TargetCocycle 718)
        (orbitP14TargetCocycle_consistent 718) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 1, 0, 2, 1, 1, 1, 2] (orbitP14RepresentativeCoeff 718)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_718))

theorem orbitP14_path_endpoint_719 :
    Order16Table.applyOrbitPath orbitP14ActionColumns [2, 0, 1, 2, 1, 1, 0, 2, 1, 2, 0]
      (orbitP14RepresentativeCoeff 719) = orbitP14TargetCoeff 719 := by
  decide +kernel

noncomputable def orbitP14NormalizeEquiv719 :
    CocycleGroup (orbitP14SelectedCocycle (orbitP14Index 719))
        (orbitP14SelectedCocycle_consistent (orbitP14Index 719)) ≃*
      CocycleGroup (orbitP14TargetCocycle 719)
        (orbitP14TargetCocycle_consistent 719) := by
  let e := Order16Table.orbitPathEquiv parent14Table parent14HBasis
    orbitP14ActionColumns orbitP14CorrectionColumns orbitP14_hbasis_cocycle
    orbitP14Aut orbitP14_action_linear [2, 0, 1, 2, 1, 1, 0, 2, 1, 2, 0] (orbitP14RepresentativeCoeff 719)
  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _
    (congrArg (Order16Table.hCocycle parent14Table parent14HBasis)
      orbitP14_path_endpoint_719))

end Smallgroups.UsefulTheorems.Order32Certificate
