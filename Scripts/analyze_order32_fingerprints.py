#!/usr/bin/env python3
"""Explore computable isomorphism fingerprints for the 51 groups of order 32."""

import argparse
import ast
import json
import subprocess
from pathlib import Path

from translate_pc import default_gap_bash, default_gap_exe

REPO = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit-lean", action="store_true")
    args = parser.parse_args()
    gap_bash = default_gap_bash()
    gap_exe = default_gap_exe(gap_bash)
    script = r'''
SizeScreen([1000000,1000000]);;
PowerCode:=function(x,g)
  local answer,i,ns;
  answer:=0;; ns:=[1,2,4,8,16,32];;
  for i in [1..6] do if x^ns[i]=One(g) then answer:=answer+2^(i-1); fi; od;
  return answer;
end;;
for id in [1..51] do
  g:=SmallGroup(32,id);; els:=Elements(g);;
  pow:=List([1,2,4,8,16,32],n->Number(els,x->x^n=One(g)));;
  cls:=SortedList(List(ConjugacyClasses(g),c->[Order(Representative(c)),Size(c)]));;
  locsig:=SortedList(List(els,x->[PowerCode(x,g),Size(Centralizer(g,x)),
    Number(els,y->y^2=x),Number(els,y->y^4=x)]));;
  Print("F|",id,"|",pow,"|",Size(Center(g)),"|",Size(DerivedSubgroup(g)),
    "|",Size(FrattiniSubgroup(g)),"|",cls,"|",locsig,"\n");
od;
QUIT;
'''
    command = [str(gap_bash), "--login", "-c", f"{gap_exe} -q"]
    result = subprocess.run(command, input=script, text=True, capture_output=True, timeout=600)
    if result.returncode:
        raise RuntimeError(result.stderr + result.stdout)
    records = {}
    raw_records = {}
    for line in result.stdout.splitlines():
        if not line.startswith("F|"):
            continue
        _, id_text, *fields = line.split("|")
        # GAP's printed lists use Python-compatible integer/list syntax.
        values = [ast.literal_eval(field) for field in fields]
        group_id = int(id_text)
        raw_records[group_id] = values
        records[group_id] = tuple(map(repr, values))
    if len(records) != 51:
        raise RuntimeError(
            f"expected 51 records, found {len(records)}; GAP stdout begins:\n{result.stdout[:4000]}"
            f"\nGAP stderr begins:\n{result.stderr[:4000]}"
        )
    for label, fields_used in [
        ("power/center/derived/Frattini", 4),
        ("plus conjugacy classes", 5),
        ("plus local root profile", 6),
    ]:
        buckets = {}
        for group_id, fingerprint in records.items():
            buckets.setdefault(fingerprint[:fields_used], []).append(group_id)
        collisions = [ids for ids in buckets.values() if len(ids) > 1]
        print(f"{label}: {len(buckets)} distinct; collisions={collisions}")
    if args.emit_lean:
        output_json = REPO / "Certificates" / "Order32" / "local_profiles.json"
        profiles = [raw_records[i][5] for i in range(1, 52)]
        output_json.write_text(
            json.dumps({"format": 1, "profiles": profiles}, indent=2) + "\n",
            encoding="utf-8",
        )
        output_dir = REPO / "Smallgroups" / "UsefulTheorems" / "Order32Certificate"
        header = """/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
"""
        profile_terms = []
        for profile in profiles:
            tuples = ", ".join(
                f"({code}, {centralizer}, {root2}, {root4})"
                for code, centralizer, root2, root4 in profile
            )
            profile_terms.append(
                f"([{tuples}] : Multiset Order32LocalFeature)"
            )
        data = [
            header.rstrip(),
            "import Smallgroups.UsefulTheorems.PGroupGeneration.LocalProfileInvariant",
            "",
            "set_option linter.style.longLine false",
            "",
            "/-! Generated candidate local profiles; every entry is recomputed by Lean. -/",
            "",
            "namespace Smallgroups.UsefulTheorems.Order32Certificate",
            "",
            "open Smallgroups.UsefulTheorems",
            "",
        ]
        data.extend([
            "",
            "end Smallgroups.UsefulTheorems.Order32Certificate",
            "",
        ])
        (output_dir / "LocalProfilesData.lean").write_text("\n".join(data), encoding="utf-8")
        part_names = []
        for group_id in range(1, 52):
            part_name = f"LocalProfilesPart{group_id:02d}"
            previous_part = part_names[-1] if part_names else None
            part_names.append(part_name)
            lines = [
                header.rstrip(),
                "import Smallgroups.UsefulTheorems.Order32Certificate.LocalProfilesData",
                f"import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart{group_id:02d}",
            ]
            if previous_part is None:
                lines.append(
                    "import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart51"
                )
            if previous_part is not None:
                lines.append(
                    f"import Smallgroups.UsefulTheorems.Order32Certificate.{previous_part}"
                )
            lines.extend([
                "",
                "set_option maxRecDepth 100000",
                "set_option linter.style.longLine false",
                "",
                f"/-! Kernel check of the local profile of `SmallGroup(32,{group_id})`. -/",
                "",
                "namespace Smallgroups.UsefulTheorems.Order32Certificate",
                "",
                "open Smallgroups.UsefulTheorems",
                "open Smallgroups.GAP",
                "",
                f"def order32LocalProfileValue{group_id} : Multiset Order32LocalFeature :=",
                f"  {profile_terms[group_id - 1]}",
                "",
                "set_option maxHeartbeats 8000000 in",
                "-- Exhaustive finite count over the 32-element imported PC group.",
                f"theorem order32_local_profile_{group_id} :",
                f"    order32LocalProfile (PCGroup smallGroup_32_{group_id}) =",
                f"      order32LocalProfileValue{group_id} := by",
                "  decide +kernel",
                "",
                "end Smallgroups.UsefulTheorems.Order32Certificate",
                "",
            ])
            (output_dir / f"{part_name}.lean").write_text("\n".join(lines), encoding="utf-8")
        identity = [header.rstrip()]
        identity.extend(
            f"import Smallgroups.UsefulTheorems.Order32Certificate.{name}"
            for name in part_names
        )
        identity.extend([
            "import Smallgroups.GAP.Order32",
            "",
            "namespace Smallgroups.UsefulTheorems.Order32Certificate",
            "",
            "open Smallgroups.UsefulTheorems",
            "open Smallgroups.GAP",
            "",
            "instance instFintypeSmallGroup32Certificate (i : Fin 51) : Fintype (smallGroup32 i) := by",
            "  unfold smallGroup32",
            "  infer_instance",
            "",
            "instance instDecidableEqSmallGroup32Certificate (i : Fin 51) :",
            "    DecidableEq (smallGroup32 i) := by",
            "  unfold smallGroup32",
            "  infer_instance",
            "",
            "def order32LocalProfileTable : Fin 51 → Multiset Order32LocalFeature :=",
            "  ![" + ",\n    ".join(
                f"order32LocalProfileValue{group_id}" for group_id in range(1, 52)
            ) + "]",
        ])
        identity.extend([
            "",
            "theorem order32_local_profile_spec (i : Fin 51) :",
            "    order32LocalProfile (smallGroup32 i) = order32LocalProfileTable i := by",
            "  fin_cases i",
        ])
        for group_id in range(1, 52):
            identity.append(f"  · exact order32_local_profile_{group_id}")
        identity.extend([
            "",
            "theorem order32LocalProfileTable_injective :",
            "    Function.Injective order32LocalProfileTable := by",
            "  decide +kernel",
            "",
            "end Smallgroups.UsefulTheorems.Order32Certificate",
            "",
        ])
        (output_dir / "LocalProfilesIdentity.lean").write_text(
            "\n".join(identity), encoding="utf-8"
        )
        print(f"wrote {output_json} and Lean local-profile modules")
    for label, selection in [
        ("local root profile only", (5,)),
        ("basic plus local root profile", (0, 1, 2, 3, 5)),
    ]:
        buckets = {}
        for group_id, fingerprint in records.items():
            key = tuple(fingerprint[i] for i in selection)
            buckets.setdefault(key, []).append(group_id)
        collisions = [ids for ids in buckets.values() if len(ids) > 1]
        print(f"{label}: {len(buckets)} distinct; collisions={collisions}")


if __name__ == "__main__":
    main()
