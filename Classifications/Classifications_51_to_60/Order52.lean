/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P

/-!
# Classification of groups of order 52

$N = 4 路 13, so there are exactly **five** groups of order $N up to isomorphism:
the cyclic group 鈩?52, 鈩?2 脳 鈩?26, 鈩?13 鈰奯{-1} 鈩?4,
鈩?13 鈰奯c 鈩?4 (where c虏 = -1 in (鈩?13)耍), and 鈩?2 脳 D_26.
This is the p = 13 (p 鈮?1 mod 4) instance of the order-4p classification in
Smallgroups.UsefulTheorems.Order4P.
-/

namespace Smallgroups.Classifications.Order52

open Smallgroups.UsefulTheorems

private instance fact_prime_13 : Fact (Nat.Prime 13) := 鉄╞y norm_num鉄?
private def c13 : (ZMod 13)耍 :=
  Units.mk0 (5 : ZMod 13) (by decide)

private theorem hcsq13 : c13 ^ 2 = (-1 : (ZMod 13)耍) := by
  unfold c13; decide

/-- 鈩?52. -/
abbrev RA : Type := fourP_I 13
/-- 鈩?2 脳 鈩?26. -/
abbrev RB : Type := fourP_II 13
/-- 鈩?13 鈰奯{-1} 鈩?4. -/
abbrev RC : Type := fourP_III 13
/-- 鈩?13 鈰奯c 鈩?4 where c虏 = -1 in (鈩?13)耍. -/
abbrev RD : Type := fourP_IV 13 c13 (by
  rw [show (4 : 鈩? = 2 * 2 from by ring, pow_mul, hcsq13, neg_one_sq])
/-- 鈩?2 脳 D_26. -/
abbrev RE : Type := fourP_V 13

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order $N is isomorphic to one of the five groups. -/
theorem classification (h : Nat.card G = 52) :
    Nonempty (G 鈮? RA) 鈭?Nonempty (G 鈮? RB) 鈭?Nonempty (G 鈮? RC) 鈭?    Nonempty (G 鈮? RD) 鈭?Nonempty (G 鈮? RE) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [RA, RB, RC, RD, RE, show (4 : 鈩? * 13 = 52 by norm_num] using
    fourP_classification_mod1 (by norm_num : Nat.Prime 13) (by norm_num : 13 % 4 = 1)
      c13 hcsq13 (h.trans (by norm_num))

/-- **(2) Distinctness & (3) Counting.** The five groups are a complete, non-redundant list of
representatives of the groups of order $N. -/
theorem isClassif : IsClassif 52 (rep5 RA RB RC RD RE) := by
  simpa [RA, RB, RC, RD, RE, show (4 : 鈩? * 13 = 52 by norm_num] using
    fourP_isClassif_mod1 (by norm_num : Nat.Prime 13) (by norm_num : 13 % 4 = 1) c13 hcsq13

/-- **The number of isomorphism classes of groups of order $N is exactly 5.** -/
theorem numIsoClasses_eq {k : 鈩晑 {rep : Fin k 鈫?Type} [鈭€ i, Group (rep i)]
    (h : IsClassif 52 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order52
