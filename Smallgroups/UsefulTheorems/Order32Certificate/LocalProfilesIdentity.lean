/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart01
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart02
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart03
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart04
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart05
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart06
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart07
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart08
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart09
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart10
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart11
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart12
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart13
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart14
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart15
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart16
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart17
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart18
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart19
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart20
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart21
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart22
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart23
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart24
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart25
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart26
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart27
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart28
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart29
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart30
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart31
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart32
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart33
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart34
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart35
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart36
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart37
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart38
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart39
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart40
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart41
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart42
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart43
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart44
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart45
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart46
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart47
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart48
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart49
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart50
import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesPart51
import Smallgroups.GAP.Order32

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems
open Smallgroups.GAP

instance instFintypeSmallGroup32Certificate (i : Fin 51) : Fintype (smallGroup32 i) := by
  unfold smallGroup32
  infer_instance

instance instDecidableEqSmallGroup32Certificate (i : Fin 51) :
    DecidableEq (smallGroup32 i) := by
  unfold smallGroup32
  infer_instance

def order32LocalProfileTable : Fin 51 → Multiset Order32LocalFeature :=
  ![order32LocalProfileValue1,
    order32LocalProfileValue2,
    order32LocalProfileValue3,
    order32LocalProfileValue4,
    order32LocalProfileValue5,
    order32LocalProfileValue6,
    order32LocalProfileValue7,
    order32LocalProfileValue8,
    order32LocalProfileValue9,
    order32LocalProfileValue10,
    order32LocalProfileValue11,
    order32LocalProfileValue12,
    order32LocalProfileValue13,
    order32LocalProfileValue14,
    order32LocalProfileValue15,
    order32LocalProfileValue16,
    order32LocalProfileValue17,
    order32LocalProfileValue18,
    order32LocalProfileValue19,
    order32LocalProfileValue20,
    order32LocalProfileValue21,
    order32LocalProfileValue22,
    order32LocalProfileValue23,
    order32LocalProfileValue24,
    order32LocalProfileValue25,
    order32LocalProfileValue26,
    order32LocalProfileValue27,
    order32LocalProfileValue28,
    order32LocalProfileValue29,
    order32LocalProfileValue30,
    order32LocalProfileValue31,
    order32LocalProfileValue32,
    order32LocalProfileValue33,
    order32LocalProfileValue34,
    order32LocalProfileValue35,
    order32LocalProfileValue36,
    order32LocalProfileValue37,
    order32LocalProfileValue38,
    order32LocalProfileValue39,
    order32LocalProfileValue40,
    order32LocalProfileValue41,
    order32LocalProfileValue42,
    order32LocalProfileValue43,
    order32LocalProfileValue44,
    order32LocalProfileValue45,
    order32LocalProfileValue46,
    order32LocalProfileValue47,
    order32LocalProfileValue48,
    order32LocalProfileValue49,
    order32LocalProfileValue50,
    order32LocalProfileValue51]

theorem order32_local_profile_spec (i : Fin 51) :
    order32LocalProfile (smallGroup32 i) = order32LocalProfileTable i := by
  fin_cases i
  · exact order32_local_profile_1
  · exact order32_local_profile_2
  · exact order32_local_profile_3
  · exact order32_local_profile_4
  · exact order32_local_profile_5
  · exact order32_local_profile_6
  · exact order32_local_profile_7
  · exact order32_local_profile_8
  · exact order32_local_profile_9
  · exact order32_local_profile_10
  · exact order32_local_profile_11
  · exact order32_local_profile_12
  · exact order32_local_profile_13
  · exact order32_local_profile_14
  · exact order32_local_profile_15
  · exact order32_local_profile_16
  · exact order32_local_profile_17
  · exact order32_local_profile_18
  · exact order32_local_profile_19
  · exact order32_local_profile_20
  · exact order32_local_profile_21
  · exact order32_local_profile_22
  · exact order32_local_profile_23
  · exact order32_local_profile_24
  · exact order32_local_profile_25
  · exact order32_local_profile_26
  · exact order32_local_profile_27
  · exact order32_local_profile_28
  · exact order32_local_profile_29
  · exact order32_local_profile_30
  · exact order32_local_profile_31
  · exact order32_local_profile_32
  · exact order32_local_profile_33
  · exact order32_local_profile_34
  · exact order32_local_profile_35
  · exact order32_local_profile_36
  · exact order32_local_profile_37
  · exact order32_local_profile_38
  · exact order32_local_profile_39
  · exact order32_local_profile_40
  · exact order32_local_profile_41
  · exact order32_local_profile_42
  · exact order32_local_profile_43
  · exact order32_local_profile_44
  · exact order32_local_profile_45
  · exact order32_local_profile_46
  · exact order32_local_profile_47
  · exact order32_local_profile_48
  · exact order32_local_profile_49
  · exact order32_local_profile_50
  · exact order32_local_profile_51

theorem order32LocalProfileTable_injective :
    Function.Injective order32LocalProfileTable := by
  decide +kernel

end Smallgroups.UsefulTheorems.Order32Certificate
