/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated kernel-checkable central extensions; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

def cocycle1 := CertifiedTableGroup.encodedCocycle parent1Table 1645655236882844667277692944970034326974182713323418372769054719
theorem cocycle1_consistent : IsCentralCocycle cocycle1 := by
  decide +kernel
abbrev generatedGroup1 := CocycleGroup cocycle1 cocycle1_consistent
theorem card_generatedGroup1 : Nat.card generatedGroup1 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle2 := CertifiedTableGroup.encodedCocycle parent2Table 848306407930016989821231158326604719525683044176528247044861983
theorem cocycle2_consistent : IsCentralCocycle cocycle2 := by
  decide +kernel
abbrev generatedGroup2 := CocycleGroup cocycle2 cocycle2_consistent
theorem card_generatedGroup2 : Nat.card generatedGroup2 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle3 := CertifiedTableGroup.encodedCocycle parent2Table 154875521659934869304647767775278009491769860428814156225188225
theorem cocycle3_consistent : IsCentralCocycle cocycle3 := by
  decide +kernel
abbrev generatedGroup3 := CocycleGroup cocycle3 cocycle3_consistent
theorem card_generatedGroup3 : Nat.card generatedGroup3 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle4 := CertifiedTableGroup.encodedCocycle parent2Table 1001964168012857788856877257113525796308012302373713587715203486
theorem cocycle4_consistent : IsCentralCocycle cocycle4 := by
  decide +kernel
abbrev generatedGroup4 := CocycleGroup cocycle4 cocycle4_consistent
theorem card_generatedGroup4 : Nat.card generatedGroup4 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle5 := CertifiedTableGroup.encodedCocycle parent3Table 87344480408439687707377776349375292498560329293835200757272757011
theorem cocycle5_consistent : IsCentralCocycle cocycle5 := by
  decide +kernel
abbrev generatedGroup5 := CocycleGroup cocycle5 cocycle5_consistent
theorem card_generatedGroup5 : Nat.card generatedGroup5 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle6 := CertifiedTableGroup.encodedCocycle parent3Table 145783860849059311700712021126879356797763143889994451016977239
theorem cocycle6_consistent : IsCentralCocycle cocycle6 := by
  decide +kernel
abbrev generatedGroup6 := CocycleGroup cocycle6 cocycle6_consistent
theorem card_generatedGroup6 : Nat.card generatedGroup6 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle7 := CertifiedTableGroup.encodedCocycle parent3Table 87224811661773568110299026835234184477026586496686559859622987844
theorem cocycle7_consistent : IsCentralCocycle cocycle7 := by
  decide +kernel
abbrev generatedGroup7 := CocycleGroup cocycle7 cocycle7_consistent
theorem card_generatedGroup7 : Nat.card generatedGroup7 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle8 := CertifiedTableGroup.encodedCocycle parent3Table 87795568253994414213720148258641375517295891789948489405244761130
theorem cocycle8_consistent : IsCentralCocycle cocycle8 := by
  decide +kernel
abbrev generatedGroup8 := CocycleGroup cocycle8 cocycle8_consistent
theorem card_generatedGroup8 : Nat.card generatedGroup8 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle9 := CertifiedTableGroup.encodedCocycle parent3Table 19886466143093925718013356981690295991480775548709087375393164
theorem cocycle9_consistent : IsCentralCocycle cocycle9 := by
  decide +kernel
abbrev generatedGroup9 := CocycleGroup cocycle9 cocycle9_consistent
theorem card_generatedGroup9 : Nat.card generatedGroup9 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle10 := CertifiedTableGroup.encodedCocycle parent3Table 589864697718738314870297904633528628109701790913221861221412322
theorem cocycle10_consistent : IsCentralCocycle cocycle10 := by
  decide +kernel
abbrev generatedGroup10 := CocycleGroup cocycle10 cocycle10_consistent
theorem card_generatedGroup10 : Nat.card generatedGroup10 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle11 := CertifiedTableGroup.encodedCocycle parent3Table 139556785305305502546850528553532350514450179199160910361758427
theorem cocycle11_consistent : IsCentralCocycle cocycle11 := by
  decide +kernel
abbrev generatedGroup11 := CocycleGroup cocycle11 cocycle11_consistent
theorem card_generatedGroup11 : Nat.card generatedGroup11 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle12 := CertifiedTableGroup.encodedCocycle parent4Table 74151111703263379498878134622900289775960399580178063831593468200
theorem cocycle12_consistent : IsCentralCocycle cocycle12 := by
  decide +kernel
abbrev generatedGroup12 := CocycleGroup cocycle12 cocycle12_consistent
theorem card_generatedGroup12 : Nat.card generatedGroup12 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle13 := CertifiedTableGroup.encodedCocycle parent4Table 327172527700197792572061484964730214706520883351154947938034631
theorem cocycle13_consistent : IsCentralCocycle cocycle13 := by
  decide +kernel
abbrev generatedGroup13 := CocycleGroup cocycle13 cocycle13_consistent
theorem card_generatedGroup13 : Nat.card generatedGroup13 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

end Smallgroups.UsefulTheorems.Order32Certificate
