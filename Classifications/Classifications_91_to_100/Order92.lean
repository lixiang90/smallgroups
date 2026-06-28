/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P

/-!
# Classification of groups of order 92

$N = 4 路 23, so there are exactly **four** groups of order $N up to isomorphism:
the cyclic group 鈩?92, 鈩?2 脳 鈩?46, 鈩?23 鈰奯{-1} 鈩?4, and 鈩?2 脳 D_46.
This is the p = 23 (p 鈮?3 mod 4) instance of the order-4p classification in
Smallgroups.UsefulTheorems.Order4P.
-/

namespace Smallgroups.Classifications.Order92

open Smallgroups.UsefulTheorems

/-- 鈩?92. -/
abbrev RA : Type := fourP_I 23
/-- 鈩?2 脳 鈩?46. -/
abbrev RB : Type := fourP_II 23
/-- 鈩?23 鈰奯{-1} 鈩?4. -/
abbrev RC : Type := fourP_III 23
/-- 鈩?2 脳 D_46. -/
abbrev RD : Type := fourP_V 23

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order $N is isomorphic to one of the four groups. -/
theorem classification (h : Nat.card G = 92) :
    Nonempty (G 鈮? RA) 鈭?Nonempty (G 鈮? RB) 鈭?Nonempty (G 鈮? RC) 鈭?    Nonempty (G 鈮? RD) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [RA, RB, RC, RD, show (4 : 鈩? * 23 = 92 by norm_num] using
    fourP_classification_mod3 (by norm_num : Nat.Prime 23) (by omega)
      (by norm_num : 23 % 4 = 3) (h.trans (by norm_num))

/-- **(2) Distinctness & (3) Counting.** The four groups are a complete, non-redundant list of
representatives of the groups of order $N. -/
theorem isClassif : IsClassif 92 (rep4 RA RB RC RD) := by
  simpa [RA, RB, RC, RD, show (4 : 鈩? * 23 = 92 by norm_num] using
    fourP_isClassif_mod3 (by norm_num : Nat.Prime 23) (by omega)
      (by norm_num : 23 % 4 = 3)

/-- **The number of isomorphism classes of groups of order $N is exactly 4.** -/
theorem numIsoClasses_eq {k : 鈩晑 {rep : Fin k 鈫?Type} [鈭€ i, Group (rep i)]
    (h : IsClassif 92 rep) : k = 4 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order92
