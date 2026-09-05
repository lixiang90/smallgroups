/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.UsefulTheorems.Order32Certificate.CocycleBasisParent01
import Smallgroups.UsefulTheorems.Order32Certificate.CocycleBasisParent02
import Smallgroups.UsefulTheorems.Order32Certificate.CocycleBasisParent03
import Smallgroups.UsefulTheorems.Order32Certificate.CocycleBasisParent04
import Smallgroups.UsefulTheorems.Order32Certificate.CocycleBasisParent05
import Smallgroups.UsefulTheorems.Order32Certificate.CocycleBasisParent07
import Smallgroups.UsefulTheorems.Order32Certificate.CocycleBasisParent10

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated kernel-checkable central extensions; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def cocycle14 := CertifiedTableGroup.encodedCocycle parent4Table 29176860476407226866896303219673235843390831401348516215851282
theorem cocycle14_consistent : IsCentralCocycle cocycle14 := by
  have hdecode : cocycle14 = Order16Table.decodeTwo parent4Table
      (synthesizeTwo coverageP4HBasis (coeffMask 3 1)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent4Table
    coverageP4HBasis orbitP4_hbasis_cocycle _
abbrev generatedGroup14 := CocycleGroup cocycle14 cocycle14_consistent
theorem card_generatedGroup14 : Nat.card generatedGroup14 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle15 := CertifiedTableGroup.encodedCocycle parent4Table 74180186559908334388193137295686519882200457913940599349998274618
theorem cocycle15_consistent : IsCentralCocycle cocycle15 := by
  have hdecode : cocycle15 = Order16Table.decodeTwo parent4Table
      (synthesizeTwo coverageP4HBasis (coeffMask 3 5)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent4Table
    coverageP4HBasis orbitP4_hbasis_cocycle _
abbrev generatedGroup15 := CocycleGroup cocycle15 cocycle15_consistent
theorem card_generatedGroup15 : Nat.card generatedGroup15 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle16 := CertifiedTableGroup.encodedCocycle parent1Table 0
theorem cocycle16_consistent : IsCentralCocycle cocycle16 := by
  have hdecode : cocycle16 = Order16Table.decodeTwo parent1Table
      (synthesizeTwo coverageP1HBasis (coeffMask 1 0)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent1Table
    coverageP1HBasis orbitP1_hbasis_cocycle _
abbrev generatedGroup16 := CocycleGroup cocycle16 cocycle16_consistent
theorem card_generatedGroup16 : Nat.card generatedGroup16 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle17 := CertifiedTableGroup.encodedCocycle parent5Table 9420911612913758323032504591917565348441426346443946510368383902
theorem cocycle17_consistent : IsCentralCocycle cocycle17 := by
  have hdecode : cocycle17 = Order16Table.decodeTwo parent5Table
      (synthesizeTwo coverageP5HBasis (coeffMask 3 6)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent5Table
    coverageP5HBasis orbitP5_hbasis_cocycle _
abbrev generatedGroup17 := CocycleGroup cocycle17 cocycle17_consistent
theorem card_generatedGroup17 : Nat.card generatedGroup17 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle18 := CertifiedTableGroup.encodedCocycle parent7Table 8534046226223639110431127286610887935693564074229354365312573402
theorem cocycle18_consistent : IsCentralCocycle cocycle18 := by
  have hdecode : cocycle18 = Order16Table.decodeTwo parent7Table
      (synthesizeTwo coverageP7HBasis (coeffMask 3 4)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent7Table
    coverageP7HBasis orbitP7_hbasis_cocycle _
abbrev generatedGroup18 := CocycleGroup cocycle18 cocycle18_consistent
theorem card_generatedGroup18 : Nat.card generatedGroup18 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle19 := CertifiedTableGroup.encodedCocycle parent7Table 9200208525824857182617424492106483035161290442054487447514170283
theorem cocycle19_consistent : IsCentralCocycle cocycle19 := by
  have hdecode : cocycle19 = Order16Table.decodeTwo parent7Table
      (synthesizeTwo coverageP7HBasis (coeffMask 3 6)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent7Table
    coverageP7HBasis orbitP7_hbasis_cocycle _
abbrev generatedGroup19 := CocycleGroup cocycle19 cocycle19_consistent
theorem card_generatedGroup19 : Nat.card generatedGroup19 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle20 := CertifiedTableGroup.encodedCocycle parent7Table 8719014320190633588991612559268332020952077030237351351290801721
theorem cocycle20_consistent : IsCentralCocycle cocycle20 := by
  have hdecode : cocycle20 = Order16Table.decodeTwo parent7Table
      (synthesizeTwo coverageP7HBasis (coeffMask 3 5)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent7Table
    coverageP7HBasis orbitP7_hbasis_cocycle _
abbrev generatedGroup20 := CocycleGroup cocycle20 cocycle20_consistent
theorem card_generatedGroup20 : Nat.card generatedGroup20 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle21 := CertifiedTableGroup.encodedCocycle parent2Table 0
theorem cocycle21_consistent : IsCentralCocycle cocycle21 := by
  have hdecode : cocycle21 = Order16Table.decodeTwo parent2Table
      (synthesizeTwo coverageP2HBasis (coeffMask 3 0)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent2Table
    coverageP2HBasis orbitP2_hbasis_cocycle _
abbrev generatedGroup21 := CocycleGroup cocycle21 cocycle21_consistent
theorem card_generatedGroup21 : Nat.card generatedGroup21 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle22 := CertifiedTableGroup.encodedCocycle parent3Table 0
theorem cocycle22_consistent : IsCentralCocycle cocycle22 := by
  have hdecode : cocycle22 = Order16Table.decodeTwo parent3Table
      (synthesizeTwo coverageP3HBasis (coeffMask 4 0)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent3Table
    coverageP3HBasis orbitP3_hbasis_cocycle _
abbrev generatedGroup22 := CocycleGroup cocycle22 cocycle22_consistent
theorem card_generatedGroup22 : Nat.card generatedGroup22 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle23 := CertifiedTableGroup.encodedCocycle parent4Table 0
theorem cocycle23_consistent : IsCentralCocycle cocycle23 := by
  have hdecode : cocycle23 = Order16Table.decodeTwo parent4Table
      (synthesizeTwo coverageP4HBasis (coeffMask 3 0)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent4Table
    coverageP4HBasis orbitP4_hbasis_cocycle _
abbrev generatedGroup23 := CocycleGroup cocycle23 cocycle23_consistent
theorem card_generatedGroup23 : Nat.card generatedGroup23 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle24 := CertifiedTableGroup.encodedCocycle parent10Table 550655328986097687367666437402591779447137221198253324522203861
theorem cocycle24_consistent : IsCentralCocycle cocycle24 := by
  have hdecode : cocycle24 = Order16Table.decodeTwo parent10Table
      (synthesizeTwo coverageP10HBasis (coeffMask 6 12)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent10Table
    coverageP10HBasis orbitP10_hbasis_cocycle _
abbrev generatedGroup24 := CocycleGroup cocycle24 cocycle24_consistent
theorem card_generatedGroup24 : Nat.card generatedGroup24 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle25 := CertifiedTableGroup.encodedCocycle parent10Table 16804326417289455606797820310971500608314340034714159185920
theorem cocycle25_consistent : IsCentralCocycle cocycle25 := by
  have hdecode : cocycle25 = Order16Table.decodeTwo parent10Table
      (synthesizeTwo coverageP10HBasis (coeffMask 6 2)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent10Table
    coverageP10HBasis orbitP10_hbasis_cocycle _
abbrev generatedGroup25 := CocycleGroup cocycle25 cocycle25_consistent
theorem card_generatedGroup25 : Nat.card generatedGroup25 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle26 := CertifiedTableGroup.encodedCocycle parent10Table 550646936054458288154420841872141953383433258135457824955804373
theorem cocycle26_consistent : IsCentralCocycle cocycle26 := by
  have hdecode : cocycle26 = Order16Table.decodeTwo parent10Table
      (synthesizeTwo coverageP10HBasis (coeffMask 6 11)) := by decide +kernel
  rw [hdecode]
  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent10Table
    coverageP10HBasis orbitP10_hbasis_cocycle _
abbrev generatedGroup26 := CocycleGroup cocycle26 cocycle26_consistent
theorem card_generatedGroup26 : Nat.card generatedGroup26 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

end Smallgroups.UsefulTheorems.Order32Certificate
