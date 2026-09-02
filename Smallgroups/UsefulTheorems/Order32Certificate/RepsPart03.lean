/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart02

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated kernel-checkable central extensions; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

def cocycle27 := CertifiedTableGroup.encodedCocycle parent11Table 36267613740552208566791647757331560592408468483493896683520
theorem cocycle27_consistent : IsCentralCocycle cocycle27 := by
  decide +kernel
abbrev generatedGroup27 := CocycleGroup cocycle27 cocycle27_consistent
theorem card_generatedGroup27 : Nat.card generatedGroup27 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle28 := CertifiedTableGroup.encodedCocycle parent11Table 19572097827195954177329226009249159532036701922784726581248
theorem cocycle28_consistent : IsCentralCocycle cocycle28 := by
  decide +kernel
abbrev generatedGroup28 := CocycleGroup cocycle28 cocycle28_consistent
theorem card_generatedGroup28 : Nat.card generatedGroup28 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle29 := CertifiedTableGroup.encodedCocycle parent11Table 550663632155533516514880999085046286868063431085662839242271445
theorem cocycle29_consistent : IsCentralCocycle cocycle29 := by
  decide +kernel
abbrev generatedGroup29 := CocycleGroup cocycle29 cocycle29_consistent
theorem card_generatedGroup29 : Nat.card generatedGroup29 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle30 := CertifiedTableGroup.encodedCocycle parent11Table 550655328986097687367666437402591779447137221198253324522203861
theorem cocycle30_consistent : IsCentralCocycle cocycle30 := by
  decide +kernel
abbrev generatedGroup30 := CocycleGroup cocycle30 cocycle30_consistent
theorem card_generatedGroup30 : Nat.card generatedGroup30 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle31 := CertifiedTableGroup.encodedCocycle parent11Table 916342469757566955725676027248229653020170521434851284948141895
theorem cocycle31_consistent : IsCentralCocycle cocycle31 := by
  decide +kernel
abbrev generatedGroup31 := CocycleGroup cocycle31 cocycle31_consistent
theorem card_generatedGroup31 : Nat.card generatedGroup31 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle32 := CertifiedTableGroup.encodedCocycle parent12Table 550663632155533516514880999085046286868063431085662839242271445
theorem cocycle32_consistent : IsCentralCocycle cocycle32 := by
  decide +kernel
abbrev generatedGroup32 := CocycleGroup cocycle32 cocycle32_consistent
theorem card_generatedGroup32 : Nat.card generatedGroup32 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle33 := CertifiedTableGroup.encodedCocycle parent13Table 64209497318650576287051771095210793315376768957262454802199837
theorem cocycle33_consistent : IsCentralCocycle cocycle33 := by
  decide +kernel
abbrev generatedGroup33 := CocycleGroup cocycle33 cocycle33_consistent
theorem card_generatedGroup33 : Nat.card generatedGroup33 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle34 := CertifiedTableGroup.encodedCocycle parent11Table 16804326417289455606797820310971500608314340034714159185920
theorem cocycle34_consistent : IsCentralCocycle cocycle34 := by
  decide +kernel
abbrev generatedGroup34 := CocycleGroup cocycle34 cocycle34_consistent
theorem card_generatedGroup34 : Nat.card generatedGroup34 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle35 := CertifiedTableGroup.encodedCocycle parent11Table 550646936054458288154420841872141953383433258135457824955804373
theorem cocycle35_consistent : IsCentralCocycle cocycle35 := by
  decide +kernel
abbrev generatedGroup35 := CocycleGroup cocycle35 cocycle35_consistent
theorem card_generatedGroup35 : Nat.card generatedGroup35 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle36 := CertifiedTableGroup.encodedCocycle parent5Table 0
theorem cocycle36_consistent : IsCentralCocycle cocycle36 := by
  decide +kernel
abbrev generatedGroup36 := CocycleGroup cocycle36 cocycle36_consistent
theorem card_generatedGroup36 : Nat.card generatedGroup36 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle37 := CertifiedTableGroup.encodedCocycle parent6Table 0
theorem cocycle37_consistent : IsCentralCocycle cocycle37 := by
  decide +kernel
abbrev generatedGroup37 := CocycleGroup cocycle37 cocycle37_consistent
theorem card_generatedGroup37 : Nat.card generatedGroup37 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle38 := CertifiedTableGroup.encodedCocycle parent10Table 24819679048656142831769857700942592387320923666302637497324554538
theorem cocycle38_consistent : IsCentralCocycle cocycle38 := by
  decide +kernel
abbrev generatedGroup38 := CocycleGroup cocycle38 cocycle38_consistent
theorem card_generatedGroup38 : Nat.card generatedGroup38 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle39 := CertifiedTableGroup.encodedCocycle parent7Table 0
theorem cocycle39_consistent : IsCentralCocycle cocycle39 := by
  decide +kernel
abbrev generatedGroup39 := CocycleGroup cocycle39 cocycle39_consistent
theorem card_generatedGroup39 : Nat.card generatedGroup39 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

end Smallgroups.UsefulTheorems.Order32Certificate
