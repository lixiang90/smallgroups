/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart01

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated kernel-checkable central extensions; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

def cocycle14 := CertifiedTableGroup.encodedCocycle parent4Table 29176860476407226866896303219673235843390831401348516215851282
theorem cocycle14_consistent : IsCentralCocycle cocycle14 := by
  decide +kernel
abbrev generatedGroup14 := CocycleGroup cocycle14 cocycle14_consistent
theorem card_generatedGroup14 : Nat.card generatedGroup14 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle15 := CertifiedTableGroup.encodedCocycle parent4Table 74180186559908334388193137295686519882200457913940599349998274618
theorem cocycle15_consistent : IsCentralCocycle cocycle15 := by
  decide +kernel
abbrev generatedGroup15 := CocycleGroup cocycle15 cocycle15_consistent
theorem card_generatedGroup15 : Nat.card generatedGroup15 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle16 := CertifiedTableGroup.encodedCocycle parent1Table 0
theorem cocycle16_consistent : IsCentralCocycle cocycle16 := by
  decide +kernel
abbrev generatedGroup16 := CocycleGroup cocycle16 cocycle16_consistent
theorem card_generatedGroup16 : Nat.card generatedGroup16 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle17 := CertifiedTableGroup.encodedCocycle parent5Table 9420911612913758323032504591917565348441426346443946510368383902
theorem cocycle17_consistent : IsCentralCocycle cocycle17 := by
  decide +kernel
abbrev generatedGroup17 := CocycleGroup cocycle17 cocycle17_consistent
theorem card_generatedGroup17 : Nat.card generatedGroup17 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle18 := CertifiedTableGroup.encodedCocycle parent7Table 8534046226223639110431127286610887935693564074229354365312573402
theorem cocycle18_consistent : IsCentralCocycle cocycle18 := by
  decide +kernel
abbrev generatedGroup18 := CocycleGroup cocycle18 cocycle18_consistent
theorem card_generatedGroup18 : Nat.card generatedGroup18 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle19 := CertifiedTableGroup.encodedCocycle parent7Table 9200208525824857182617424492106483035161290442054487447514170283
theorem cocycle19_consistent : IsCentralCocycle cocycle19 := by
  decide +kernel
abbrev generatedGroup19 := CocycleGroup cocycle19 cocycle19_consistent
theorem card_generatedGroup19 : Nat.card generatedGroup19 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle20 := CertifiedTableGroup.encodedCocycle parent7Table 8719014320190633588991612559268332020952077030237351351290801721
theorem cocycle20_consistent : IsCentralCocycle cocycle20 := by
  decide +kernel
abbrev generatedGroup20 := CocycleGroup cocycle20 cocycle20_consistent
theorem card_generatedGroup20 : Nat.card generatedGroup20 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle21 := CertifiedTableGroup.encodedCocycle parent2Table 0
theorem cocycle21_consistent : IsCentralCocycle cocycle21 := by
  decide +kernel
abbrev generatedGroup21 := CocycleGroup cocycle21 cocycle21_consistent
theorem card_generatedGroup21 : Nat.card generatedGroup21 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle22 := CertifiedTableGroup.encodedCocycle parent3Table 0
theorem cocycle22_consistent : IsCentralCocycle cocycle22 := by
  decide +kernel
abbrev generatedGroup22 := CocycleGroup cocycle22 cocycle22_consistent
theorem card_generatedGroup22 : Nat.card generatedGroup22 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle23 := CertifiedTableGroup.encodedCocycle parent4Table 0
theorem cocycle23_consistent : IsCentralCocycle cocycle23 := by
  decide +kernel
abbrev generatedGroup23 := CocycleGroup cocycle23 cocycle23_consistent
theorem card_generatedGroup23 : Nat.card generatedGroup23 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle24 := CertifiedTableGroup.encodedCocycle parent10Table 550655328986097687367666437402591779447137221198253324522203861
theorem cocycle24_consistent : IsCentralCocycle cocycle24 := by
  decide +kernel
abbrev generatedGroup24 := CocycleGroup cocycle24 cocycle24_consistent
theorem card_generatedGroup24 : Nat.card generatedGroup24 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle25 := CertifiedTableGroup.encodedCocycle parent10Table 16804326417289455606797820310971500608314340034714159185920
theorem cocycle25_consistent : IsCentralCocycle cocycle25 := by
  decide +kernel
abbrev generatedGroup25 := CocycleGroup cocycle25 cocycle25_consistent
theorem card_generatedGroup25 : Nat.card generatedGroup25 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle26 := CertifiedTableGroup.encodedCocycle parent10Table 550646936054458288154420841872141953383433258135457824955804373
theorem cocycle26_consistent : IsCentralCocycle cocycle26 := by
  decide +kernel
abbrev generatedGroup26 := CocycleGroup cocycle26 cocycle26_consistent
theorem card_generatedGroup26 : Nat.card generatedGroup26 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

end Smallgroups.UsefulTheorems.Order32Certificate
