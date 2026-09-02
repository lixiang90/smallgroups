/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.Tables
import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart03

set_option maxRecDepth 100000
set_option linter.style.longLine false

/-! Generated kernel-checkable central extensions; do not edit. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

def cocycle40 := CertifiedTableGroup.encodedCocycle parent8Table 0
theorem cocycle40_consistent : IsCentralCocycle cocycle40 := by
  decide +kernel
abbrev generatedGroup40 := CocycleGroup cocycle40 cocycle40_consistent
theorem card_generatedGroup40 : Nat.card generatedGroup40 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle41 := CertifiedTableGroup.encodedCocycle parent9Table 0
theorem cocycle41_consistent : IsCentralCocycle cocycle41 := by
  decide +kernel
abbrev generatedGroup41 := CocycleGroup cocycle41 cocycle41_consistent
theorem card_generatedGroup41 : Nat.card generatedGroup41 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle42 := CertifiedTableGroup.encodedCocycle parent11Table 24723879383033016325243632861578134177624475007263797297535878326
theorem cocycle42_consistent : IsCentralCocycle cocycle42 := by
  decide +kernel
abbrev generatedGroup42 := CocycleGroup cocycle42 cocycle42_consistent
theorem card_generatedGroup42 : Nat.card generatedGroup42 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle43 := CertifiedTableGroup.encodedCocycle parent11Table 24723852830103064421385406104477514914256422704806453269727085750
theorem cocycle43_consistent : IsCentralCocycle cocycle43 := by
  decide +kernel
abbrev generatedGroup43 := CocycleGroup cocycle43 cocycle43_consistent
theorem card_generatedGroup43 : Nat.card generatedGroup43 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle44 := CertifiedTableGroup.encodedCocycle parent11Table 25221049503854337361016349334312632326723510943223223441190104675
theorem cocycle44_consistent : IsCentralCocycle cocycle44 := by
  decide +kernel
abbrev generatedGroup44 := CocycleGroup cocycle44 cocycle44_consistent
theorem card_generatedGroup44 : Nat.card generatedGroup44 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle45 := CertifiedTableGroup.encodedCocycle parent10Table 0
theorem cocycle45_consistent : IsCentralCocycle cocycle45 := by
  decide +kernel
abbrev generatedGroup45 := CocycleGroup cocycle45 cocycle45_consistent
theorem card_generatedGroup45 : Nat.card generatedGroup45 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle46 := CertifiedTableGroup.encodedCocycle parent11Table 0
theorem cocycle46_consistent : IsCentralCocycle cocycle46 := by
  decide +kernel
abbrev generatedGroup46 := CocycleGroup cocycle46 cocycle46_consistent
theorem card_generatedGroup46 : Nat.card generatedGroup46 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle47 := CertifiedTableGroup.encodedCocycle parent12Table 0
theorem cocycle47_consistent : IsCentralCocycle cocycle47 := by
  decide +kernel
abbrev generatedGroup47 := CocycleGroup cocycle47 cocycle47_consistent
theorem card_generatedGroup47 : Nat.card generatedGroup47 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle48 := CertifiedTableGroup.encodedCocycle parent13Table 0
theorem cocycle48_consistent : IsCentralCocycle cocycle48 := by
  decide +kernel
abbrev generatedGroup48 := CocycleGroup cocycle48 cocycle48_consistent
theorem card_generatedGroup48 : Nat.card generatedGroup48 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle49 := CertifiedTableGroup.encodedCocycle parent14Table 15388641137742743967023279990056589228040863048173415596032
theorem cocycle49_consistent : IsCentralCocycle cocycle49 := by
  decide +kernel
abbrev generatedGroup49 := CocycleGroup cocycle49 cocycle49_consistent
theorem card_generatedGroup49 : Nat.card generatedGroup49 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle50 := CertifiedTableGroup.encodedCocycle parent14Table 462065616998279838356705657418246325220618638082207644847023089
theorem cocycle50_consistent : IsCentralCocycle cocycle50 := by
  decide +kernel
abbrev generatedGroup50 := CocycleGroup cocycle50 cocycle50_consistent
theorem card_generatedGroup50 : Nat.card generatedGroup50 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

def cocycle51 := CertifiedTableGroup.encodedCocycle parent14Table 0
theorem cocycle51_consistent : IsCentralCocycle cocycle51 := by
  decide +kernel
abbrev generatedGroup51 := CocycleGroup cocycle51 cocycle51_consistent
theorem card_generatedGroup51 : Nat.card generatedGroup51 = 32 := by
  rw [CocycleGroup.card_eq]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

end Smallgroups.UsefulTheorems.Order32Certificate
