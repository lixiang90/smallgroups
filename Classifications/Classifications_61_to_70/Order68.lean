/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order4P

/-!
# Classification of groups of order 68

$N = 4 路 17, so there are exactly **five** groups of order $N up to isomorphism:
the cyclic group 鈩?68, 鈩?2 脳 鈩?34, 鈩?17 鈰奯{-1} 鈩?4,
鈩?17 鈰奯c 鈩?4 (where c虏 = -1 in (鈩?17)耍), and 鈩?2 脳 D_34.
This is the p = 17 (p 鈮?1 mod 4) instance of the order-4p classification in
Smallgroups.UsefulTheorems.Order4P.
-/

namespace Smallgroups.Classifications.Order68

open Smallgroups.UsefulTheorems

private instance fact_prime_17 : Fact (Nat.Prime 17) := 鉄╞y norm_num鉄?
private def c17 : (ZMod 17)耍 :=
  Units.mk0 (4 : ZMod 17) (by decide)

private theorem hcsq17 : c17 ^ 2 = (-1 : (ZMod 17)耍) := by
  unfold c17; decide

/-- 鈩?68. -/
abbrev RA : Type := fourP_I 17
/-- 鈩?2 脳 鈩?34. -/
abbrev RB : Type := fourP_II 17
/-- 鈩?17 鈰奯{-1} 鈩?4. -/
abbrev RC : Type := fourP_III 17
/-- 鈩?17 鈰奯c 鈩?4 where c虏 = -1 in (鈩?17)耍. -/
abbrev RD : Type := fourP_IV 17 c17 (by
  rw [show (4 : 鈩? = 2 * 2 from by ring, pow_mul, hcsq17, neg_one_sq])
/-- 鈩?2 脳 D_34. -/
abbrev RE : Type := fourP_V 17

variable {G : Type*} [Group G]

/-- **(1) Exhaustiveness.** Every group of order $N is isomorphic to one of the five groups. -/
theorem classification (h : Nat.card G = 68) :
    Nonempty (G 鈮? RA) 鈭?Nonempty (G 鈮? RB) 鈭?Nonempty (G 鈮? RC) 鈭?    Nonempty (G 鈮? RD) 鈭?Nonempty (G 鈮? RE) := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  simpa [RA, RB, RC, RD, RE, show (4 : 鈩? * 17 = 68 by norm_num] using
    fourP_classification_mod1 (by norm_num : Nat.Prime 17) (by norm_num : 17 % 4 = 1)
      c17 hcsq17 (h.trans (by norm_num))

/-- **(2) Distinctness & (3) Counting.** The five groups are a complete, non-redundant list of
representatives of the groups of order $N. -/
theorem isClassif : IsClassif 68 (rep5 RA RB RC RD RE) := by
  simpa [RA, RB, RC, RD, RE, show (4 : 鈩? * 17 = 68 by norm_num] using
    fourP_isClassif_mod1 (by norm_num : Nat.Prime 17) (by norm_num : 17 % 4 = 1) c17 hcsq17

/-- **The number of isomorphism classes of groups of order $N is exactly 5.** -/
theorem numIsoClasses_eq {k : 鈩晑 {rep : Fin k 鈫?Type} [鈭€ i, Group (rep i)]
    (h : IsClassif 68 rep) : k = 5 :=
  (isClassif.card_unique h).symm

end Smallgroups.Classifications.Order68
