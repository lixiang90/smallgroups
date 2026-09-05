#!/usr/bin/env python3
"""Generate GF(2) central-extension certificates for all groups of order 16.

The generator asks GAP only for multiplication tables, automorphism generators, and
the final ``IdGroup`` lookup.  Cocycle equations, coboundaries, quotient bases, and
automorphism orbits are computed independently over GF(2) here.  The JSON output is
intended as untrusted input to the Lean checker in ``FiniteCohomology.lean``.

Use ``--summary`` while developing; it performs all computations but does not write a
certificate file.
"""

from __future__ import annotations

import argparse
from collections import deque
import json
import subprocess
import tempfile
from pathlib import Path

from translate_pc import default_gap_bash, default_gap_exe

REPO = Path(__file__).resolve().parent.parent


def run_gap(script: str, gap_bash: Path, gap_exe: str, timeout: int = 600) -> str:
    cmd = [str(gap_bash), "--login", "-c", f"{gap_exe} -q"]
    res = subprocess.run(cmd, input=script, capture_output=True, text=True, timeout=timeout)
    if res.returncode != 0:
        raise RuntimeError(f"GAP failed:\n{res.stderr}\n{res.stdout}")
    return res.stdout.replace("\r", "")


def gap_order16_data(gap_bash: Path, gap_exe: str):
    script = r'''
for id in [1..14] do
  g := SmallGroup(16,id);
  els := ShallowCopy(Elements(g));
  onepos := Position(els,One(g));
  tmp := els[1]; els[1] := els[onepos]; els[onepos] := tmp;
  Print("GROUP ",id,"\n");
  for a in [1..16] do
    Print("M");
    for b in [1..16] do Print(" ",Position(els,els[a]*els[b])-1); od;
    Print("\n");
  od;
  autgens := GeneratorsOfGroup(AutomorphismGroup(g));
  for aut in autgens do
    Print("A");
    for a in [1..16] do Print(" ",Position(els,Image(aut,els[a]))-1); od;
    Print("\n");
  od;
  pcgs:=Pcgs(g);
  for a in [1..16] do
    Print("P");
    for exponent in ExponentsOfPcElement(pcgs,els[a]) do Print(" ",exponent); od;
    Print("\n");
  od;
  Print("END\n");
od;
QUIT;
'''
    out = run_gap(script, gap_bash, gap_exe)
    groups = []
    current = None
    for raw in out.splitlines():
        line = raw.strip()
        if line.startswith("GROUP "):
            current = {"gap16_id": int(line.split()[1]), "mul": [], "aut_generators": [],
                       "pc_exponents": []}
            groups.append(current)
        elif line.startswith("M "):
            current["mul"].append([int(x) for x in line.split()[1:]])
        elif line.startswith("A "):
            current["aut_generators"].append([int(x) for x in line.split()[1:]])
        elif line.startswith("P "):
            current["pc_exponents"].append([int(x) for x in line.split()[1:]])
        elif line == "END":
            current = None
    if [g["gap16_id"] for g in groups] != list(range(1, 15)):
        raise RuntimeError("GAP did not return exactly SmallGroup(16,1..14)")
    for g in groups:
        if len(g["mul"]) != 16 or any(len(row) != 16 for row in g["mul"]):
            raise RuntimeError(f"bad multiplication table for SmallGroup(16,{g['gap16_id']})")
        if len(g["pc_exponents"]) != 16 or any(len(row) != 4 for row in g["pc_exponents"]):
            raise RuntimeError(f"bad PC exponent map for SmallGroup(16,{g['gap16_id']})")
        for permutation in g["aut_generators"]:
            if sorted(permutation) != list(range(16)) or any(
                permutation[g["mul"][a][b]] != g["mul"][permutation[a]][permutation[b]]
                for a in range(16) for b in range(16)
            ):
                raise RuntimeError(
                    f"bad automorphism permutation for SmallGroup(16,{g['gap16_id']})"
                )
        g["inv"] = [next(b for b in range(16) if g["mul"][b][a] == 0) for a in range(16)]
    return groups


def add_echelon(pivots: dict[int, tuple[int, int]], vector: int, label: int) -> bool:
    """Insert ``vector`` and its coordinate label into an RREF-like GF(2) basis."""
    while vector:
        col = (vector & -vector).bit_length() - 1
        if col in pivots:
            row, combo = pivots[col]
            vector ^= row
            label ^= combo
        else:
            for p, (row, combo) in list(pivots.items()):
                if (row >> col) & 1:
                    pivots[p] = (row ^ vector, combo ^ label)
            pivots[col] = (vector, label)
            return True
    return False


def independent(vectors: list[int]) -> list[int]:
    pivots = {}
    result = []
    for vector in vectors:
        if add_echelon(pivots, vector, 0):
            result.append(vector)
    return result


def kernel_basis(rows: list[int], dimension: int) -> list[int]:
    rows = list({row for row in rows if row})
    pivot_columns = []
    rank = 0
    for col in range(dimension):
        found = next((i for i in range(rank, len(rows)) if (rows[i] >> col) & 1), None)
        if found is None:
            continue
        rows[rank], rows[found] = rows[found], rows[rank]
        pivot = rows[rank]
        for i, row in enumerate(rows):
            if i != rank and ((row >> col) & 1):
                rows[i] = row ^ pivot
        pivot_columns.append(col)
        rank += 1
        if rank == len(rows):
            break
    pivot_rows = dict(zip(pivot_columns, rows[:rank]))
    pivot_cols = set(pivot_columns)
    result = []
    for free in range(dimension):
        if free in pivot_cols:
            continue
        vector = 1 << free
        for pivot, row in pivot_rows.items():
            if (row >> free) & 1:
                vector |= 1 << pivot
        result.append(vector)
    return result


def coordinate_solver(basis: list[int]):
    pivots: dict[int, tuple[int, int]] = {}
    for i, vector in enumerate(basis):
        if not add_echelon(pivots, vector, 1 << i):
            raise RuntimeError("coordinate basis is dependent")

    def solve(vector: int) -> int:
        answer = 0
        while vector:
            col = (vector & -vector).bit_length() - 1
            if col not in pivots:
                raise RuntimeError("vector is outside advertised span")
            row, combo = pivots[col]
            vector ^= row
            answer ^= combo
        return answer

    return solve


def coordinate_reducer(basis: list[int]):
    """Return a linear coordinate projection defined on the whole ambient space.

    On the span of ``basis`` it is the inverse of synthesis.  Away from the span,
    nonpivot coordinates are simply discarded.  Generated Lean certificates verify
    the resulting projection modulo the selected cocycle equations.
    """
    pivots: dict[int, tuple[int, int]] = {}
    for i, vector in enumerate(basis):
        if not add_echelon(pivots, vector, 1 << i):
            raise RuntimeError("coordinate basis is dependent")

    def reduce(vector: int) -> int:
        answer = 0
        while vector:
            col = (vector & -vector).bit_length() - 1
            if col in pivots:
                row, combo = pivots[col]
                vector ^= row
                answer ^= combo
            else:
                vector ^= 1 << col
        return answer

    return reduce


def spanning_solver(vectors: list[int]):
    """Solve in a possibly redundant spanning family, returning a bit-mask label."""
    pivots: dict[int, tuple[int, int]] = {}
    for i, vector in enumerate(vectors):
        add_echelon(pivots, vector, 1 << i)

    def solve(vector: int) -> int:
        answer = 0
        while vector:
            col = (vector & -vector).bit_length() - 1
            if col not in pivots:
                raise RuntimeError("vector is outside advertised span")
            row, combo = pivots[col]
            vector ^= row
            answer ^= combo
        return answer

    return solve


def xor_vectors(vectors: list[int], mask: int) -> int:
    answer = 0
    i = 0
    while mask:
        if mask & 1:
            answer ^= vectors[i]
        mask >>= 1
        i += 1
    return answer


def cocycle_data(group):
    mul = group["mul"]
    # Normalization removes row/column 0: 15*15 rather than 16*16 variables.
    def variable(a: int, b: int):
        return None if a == 0 or b == 0 else (a - 1) * 15 + (b - 1)

    def toggle(row: int, a: int, b: int) -> int:
        v = variable(a, b)
        return row if v is None else row ^ (1 << v)

    equations = []
    equation_records = []
    for a in range(16):
        for b in range(16):
            for c in range(16):
                row = 0
                row = toggle(row, a, b)
                row = toggle(row, mul[a][b], c)
                row = toggle(row, b, c)
                row = toggle(row, a, mul[b][c])
                if row:
                    equations.append(row)
                    equation_records.append(((a, b, c), row))
    z_basis = kernel_basis(equations, 225)
    if any(any((vector & row).bit_count() % 2 for row in equations) for vector in z_basis):
        raise RuntimeError(f"invalid Z2 kernel basis for SmallGroup(16,{group['gap16_id']})")

    coboundaries = []
    for q in range(1, 16):
        vector = 0
        for a in range(1, 16):
            for b in range(1, 16):
                bit = (1 if a == q else 0) ^ (1 if b == q else 0)
                bit ^= 1 if mul[a][b] == q else 0
                if bit:
                    vector ^= 1 << variable(a, b)
        coboundaries.append((vector, 1 << (q - 1)))
    b_pivots = {}
    b_basis = []
    d_basis = []
    for vector, source in coboundaries:
        if add_echelon(b_pivots, vector, 0):
            b_basis.append(vector)
            d_basis.append(source)

    span_pivots = {}
    for vector in b_basis:
        add_echelon(span_pivots, vector, 0)
    h_basis = []
    for vector in z_basis:
        if add_echelon(span_pivots, vector, 0):
            h_basis.append(vector)

    total_basis = b_basis + h_basis
    solve = coordinate_solver(total_basis)
    reduce_coordinates = coordinate_reducer(total_basis)
    bdim = len(b_basis)
    for vector in z_basis:
        try:
            solve(vector)
        except RuntimeError as exc:
            raise RuntimeError(
                f"Z2 basis does not span itself for SmallGroup(16,{group['gap16_id']})"
            ) from exc

    equation_pivots = {}
    equation_basis = []
    equation_triples = []
    for triple, row in equation_records:
        if add_echelon(equation_pivots, row, 0):
            equation_basis.append(row)
            equation_triples.append(triple)
    if len(equation_basis) + len(total_basis) != 225:
        raise RuntimeError(
            f"rank/nullity mismatch for SmallGroup(16,{group['gap16_id']})"
        )

    coordinate_columns = [reduce_coordinates(1 << p) for p in range(225)]
    coordinate_rows = []
    for i in range(len(total_basis)):
        row = 0
        for p, column in enumerate(coordinate_columns):
            if (column >> i) & 1:
                row ^= 1 << p
        coordinate_rows.append(row)

    # A right inverse of the independent equation rows.
    equation_columns = []
    for p in range(225):
        column = 0
        for j, row in enumerate(equation_basis):
            if (row >> p) & 1:
                column ^= 1 << j
        equation_columns.append(column)
    solve_equations = spanning_solver(equation_columns)
    correction_columns = []
    for j in range(len(equation_basis)):
        q = solve_equations(1 << j)
        correction_columns.append(q ^ xor_vectors(total_basis, reduce_coordinates(q)))

    for p in range(225):
        lhs = xor_vectors(total_basis, coordinate_columns[p])
        equation_values = 0
        for j, row in enumerate(equation_basis):
            if (row >> p) & 1:
                equation_values ^= 1 << j
        lhs ^= xor_vectors(correction_columns, equation_values)
        if lhs != 1 << p:
            raise RuntimeError(
                f"invalid BC+RE identity for SmallGroup(16,{group['gap16_id']}) at {p}"
            )

    def transport(vector: int, permutation: list[int]) -> int:
        answer = 0
        for a in range(1, 16):
            for b in range(1, 16):
                old = variable(permutation[a], permutation[b])
                if (vector >> old) & 1:
                    answer ^= 1 << variable(a, b)
        return answer

    action_generators = []
    action_correction_generators = []
    for permutation in group["aut_generators"]:
        columns = []
        correction_columns_for_generator = []
        for vector in h_basis:
            transported = transport(vector, permutation)
            if any((transported & row).bit_count() % 2 for row in equations):
                raise RuntimeError(
                    f"automorphism does not preserve Z2 for SmallGroup(16,{group['gap16_id']})"
                )
            coordinates = solve(transported)
            columns.append(coordinates >> bdim)
            b_coordinates = coordinates & ((1 << bdim) - 1)
            correction_columns_for_generator.append(xor_vectors(d_basis, b_coordinates))
        action_generators.append(columns)
        action_correction_generators.append(correction_columns_for_generator)

    def apply_matrix(columns: list[int], vector: int) -> int:
        return xor_vectors(columns, vector)

    unseen = set(range(1 << len(h_basis)))
    orbit_reps = []
    orbit_paths = {}
    orbit_words = {}
    identity_permutation = list(range(16))
    while unseen:
        seed = min(unseen)
        orbit = {seed}
        frontier = deque([seed])
        paths = {seed: identity_permutation}
        words = {seed: []}
        while frontier:
            v = frontier.popleft()
            for generator_index, (matrix, permutation) in enumerate(
                zip(action_generators, group["aut_generators"])
            ):
                w = apply_matrix(matrix, v)
                if w not in orbit:
                    orbit.add(w)
                    frontier.append(w)
                    # `transport(transport(f, p), g) = transport(f, p ∘ g)`.
                    paths[w] = [paths[v][permutation[a]] for a in range(16)]
                    words[w] = words[v] + [generator_index]
        unseen.difference_update(orbit)
        rep = min(orbit)
        if rep != seed:
            raise RuntimeError("orbit seed is not its minimum representative")
        orbit_index = len(orbit_reps)
        orbit_reps.append(rep)
        for h_mask, permutation in paths.items():
            orbit_paths[h_mask] = (orbit_index, permutation)
            orbit_words[h_mask] = words[h_mask]

    orbit_normalizations = []
    for h_mask in range(1 << len(h_basis)):
        orbit_index, permutation = orbit_paths[h_mask]
        rep_mask = orbit_reps[orbit_index]
        transported_rep = transport(xor_vectors(h_basis, rep_mask), permutation)
        h_cocycle = xor_vectors(h_basis, h_mask)
        delta = transported_rep ^ h_cocycle
        coordinates = solve(delta)
        if coordinates >> bdim:
            raise RuntimeError(
                f"orbit correction has a nonzero H2 coordinate for "
                f"SmallGroup(16,{group['gap16_id']}), mask {h_mask}"
            )
        d_mask = xor_vectors(d_basis, coordinates)
        if xor_vectors(b_basis, coordinates) != delta:
            raise RuntimeError(
                f"invalid orbit coboundary correction for "
                f"SmallGroup(16,{group['gap16_id']}), mask {h_mask}"
            )
        orbit_normalizations.append({
            "h2_mask": h_mask,
            "orbit_index": orbit_index,
            "representative_mask": rep_mask,
            "permutation": permutation,
            "one_cochain": d_mask,
        })

    group.update({
        "z2_dimension": len(z_basis),
        "b2_dimension": len(b_basis),
        "h2_dimension": len(h_basis),
        "b2_basis": b_basis,
        "b2_preimages": d_basis,
        "h2_basis": h_basis,
        "coordinate_rows": coordinate_rows,
        "coordinate_columns": coordinate_columns,
        "equation_triples": equation_triples,
        "equation_columns": equation_columns,
        "correction_columns": correction_columns,
        "h2_action_generators": action_generators,
        "h2_action_correction_generators": action_correction_generators,
        "orbit_representatives": orbit_reps,
        "orbit_words": [orbit_words[k] for k in range(1 << len(h_basis))],
        "orbit_normalizations": orbit_normalizations,
    })
    return group


def extension_table(mul: list[list[int]], cocycle: int):
    def value(a: int, b: int) -> int:
        if a == 0 or b == 0:
            return 0
        return (cocycle >> ((a - 1) * 15 + (b - 1))) & 1

    table = []
    for a in range(16):
        for x in range(2):
            row = []
            for b in range(16):
                for y in range(2):
                    row.append(2 * mul[a][b] + (x ^ y ^ value(a, b)) + 1)
            table.append(row)
    return table


def refresh_shortest_orbit_words(group):
    """Recompute shortest generator words from already certified H² action columns."""
    generators = group["h2_action_generators"]

    def apply_matrix(columns, vector):
        return xor_vectors(columns, vector)

    words_by_mask = {}
    unseen = set(range(1 << group["h2_dimension"]))
    representatives = []
    while unseen:
        seed = min(unseen)
        representatives.append(seed)
        frontier = deque([seed])
        words = {seed: []}
        while frontier:
            vector = frontier.popleft()
            for generator_index, matrix in enumerate(generators):
                image = apply_matrix(matrix, vector)
                if image not in words:
                    words[image] = words[vector] + [generator_index]
                    frontier.append(image)
        unseen.difference_update(words)
        words_by_mask.update(words)
    if representatives != group["orbit_representatives"]:
        raise RuntimeError(
            f"shortest-word orbit representatives changed for parent {group['gap16_id']}"
        )
    group["orbit_words"] = [words_by_mask[k] for k in range(1 << group["h2_dimension"])]


def build_orbit_forest(group):
    """Compress shortest orbit words to one checked predecessor edge per H² vector."""
    words = group["orbit_words"]
    normalizations = group["orbit_normalizations"]
    actions = group["h2_action_generators"]
    lookup = {}
    for vector, word in enumerate(words):
        orbit = normalizations[vector]["orbit_index"]
        key = (orbit, tuple(word))
        if key in lookup:
            raise RuntimeError(
                f"duplicate orbit-forest path for parent {group['gap16_id']}: {key}"
            )
        lookup[key] = vector

    parents = []
    generators = []
    ranks = []
    for vector, word in enumerate(words):
        rank = len(word)
        ranks.append(rank)
        if rank == 0:
            parents.append(vector)
            generators.append(0)
            continue
        orbit = normalizations[vector]["orbit_index"]
        parent = lookup[(orbit, tuple(word[:-1]))]
        generator = word[-1]
        if xor_vectors(actions[generator], parent) != vector:
            raise RuntimeError(
                f"bad orbit-forest edge for parent {group['gap16_id']}, vector {vector}"
            )
        parents.append(parent)
        generators.append(generator)

    group["orbit_forest_parent"] = parents
    group["orbit_forest_generator"] = generators
    group["orbit_forest_rank"] = ranks


def identify_extensions(groups, gap_bash: Path, gap_exe: str):
    records = []
    script = []
    for group in groups:
        for orbit_index, mask in enumerate(group["orbit_representatives"]):
            cocycle = xor_vectors(group["h2_basis"], mask)
            table = extension_table(group["mul"], cocycle)
            gap_table = "[" + ",".join("[" + ",".join(map(str, row)) + "]" for row in table) + "]"
            script.append(f"tbl:={gap_table};; g:=GroupByMultiplicationTable(tbl);;")
            script.append("els:=Elements(g);; if MultiplicationTable(els)<>tbl then Error(\"table order changed\"); fi;;")
            script.append(
                f'Print("ID {group["gap16_id"]} {orbit_index} ",IdGroup(g)[2],"\\n");'
            )
            records.append((group, orbit_index, cocycle))
    script.append("QUIT;")
    out = run_gap("\n".join(script), gap_bash, gap_exe, timeout=1200)
    ids = {}
    for line in out.splitlines():
        if line.startswith("ID "):
            _, parent, orbit, child = line.split()
            ids[(int(parent), int(orbit))] = int(child)
    if len(ids) != len(records):
        raise RuntimeError(f"GAP identified {len(ids)} of {len(records)} extensions")
    map_script = []
    for group, orbit_index, cocycle in records:
        table = extension_table(group["mul"], cocycle)
        gap_table = "[" + ",".join("[" + ",".join(map(str, row)) + "]" for row in table) + "]"
        child = ids[(group["gap16_id"], orbit_index)]
        map_script.extend([
            f"tbl:={gap_table};; g:=GroupByMultiplicationTable(tbl);; els:=Elements(g);;",
            "if MultiplicationTable(els)<>tbl then Error(\"table order changed\"); fi;;",
            f"h:=SmallGroup(32,{child});; iso:=IsomorphismGroups(g,h);; pcgs:=Pcgs(h);;",
            f'for idx in [1..32] do Print("E {group["gap16_id"]} {orbit_index} ",idx-1); '
            'for e in ExponentsOfPcElement(pcgs,Image(iso,els[idx])) do Print(" ",e); od; '
            'Print("\\n"); od;',
        ])
    map_script.append("QUIT;")
    map_out = run_gap("\n".join(map_script), gap_bash, gap_exe, timeout=1200)
    exponent_rows = {}
    for line in map_out.splitlines():
        if line.startswith("E "):
            values = [int(x) for x in line.split()[1:]]
            parent, orbit, index = values[:3]
            row = values[3:]
            if len(row) != 5:
                raise RuntimeError(f"bad pc exponent row for parent {parent}, orbit {orbit}")
            exponent_rows[(parent, orbit, index)] = row
    exponent_maps = {}
    for group, orbit_index, _ in records:
        key = (group["gap16_id"], orbit_index)
        try:
            exponent_maps[key] = [exponent_rows[key + (i,)] for i in range(32)]
        except KeyError as exc:
            raise RuntimeError(f"incomplete pc exponent map for parent/orbit {key}") from exc
    for group in groups:
        group["extensions"] = []
        for orbit_index, mask in enumerate(group["orbit_representatives"]):
            group["extensions"].append({
                "orbit_index": orbit_index,
                "h2_mask": mask,
                "cocycle": xor_vectors(group["h2_basis"], mask),
                "gap32_id": ids[(group["gap16_id"], orbit_index)],
                "pc_exponents": exponent_maps[(group["gap16_id"], orbit_index)],
            })


def lean_vector(values):
    return "![" + ", ".join(str(x) for x in values) + "]"


def lean_zmod2_vector(values):
    return "![" + ", ".join(f"({x} : ZMod 2)" for x in values) + "]"


def relation_alignment_lines(source_type, stem, forward, result, child, exponents, card_proof):
    """Emit a PC-tower map checked by layer relations and one explicit right inverse."""
    inverse = [None] * 32
    for source_index, row in enumerate(exponents):
        target_index = sum(bit << index for index, bit in enumerate(row))
        if not 0 <= target_index < 32 or inverse[target_index] is not None:
            raise RuntimeError(f"non-permutation exponent table for SmallGroup(32,{child})")
        inverse[target_index] = source_index
    if any(index is None for index in inverse):
        raise RuntimeError(f"incomplete exponent table for SmallGroup(32,{child})")
    generator_preimages = [inverse[1 << index] for index in range(5)]
    layers = [f"sg32_{child}_L{index}" for index in range(1, 6)]
    lines = [
        "-- The per-layer relation certificates require a larger kernel-reduction budget.",
        "set_option maxHeartbeats 8000000",
        "",
        f"def {stem}FromIndex (i : Fin 32) : {source_type} where",
        "  fst := ((i.val % 2 : ℕ) : ZMod 2)",
        "  snd := ⟨⟨i.val / 2, by omega⟩⟩",
        "",
        f"def {stem}Map0 : pcTower [] →* {source_type} where",
        "  toFun _ := 1",
        "  map_one' := rfl",
        "  map_mul' _ _ := (mul_one 1).symm",
        "",
    ]
    for depth in range(5, 1, -1):
        tail = layers[depth - 1:]
        current = layers[depth - 1]
        tower = ", ".join(layers[depth - 1:])
        rest = ", ".join(tail[1:])
        rest_list = f"[{rest}]" if rest else "[]"
        lines.extend([
            f"def {stem}Map{depth} : pcTower [{tower}] →* {source_type} :=",
            f"  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData {current} {rest_list})",
            f"    {stem}Map{depth + 1 if depth < 5 else 0} ({stem}FromIndex {generator_preimages[depth - 1]})",
            "    (by decide +kernel)",
            "",
        ])
    rest = ", ".join(layers[1:])
    lines.extend([
        f"def {stem}ToSource : PCGroup smallGroup_32_{child} →* {source_type} :=",
        f"  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData {layers[0]} [{rest}])",
        f"    {stem}Map2 ({stem}FromIndex {generator_preimages[0]}) (by decide +kernel)",
        "",
        "set_option maxHeartbeats 8000000 in",
        "-- Kernel reduction checks the finite pc relations and explicit right inverse.",
        f"noncomputable def {result} :",
        f"    {source_type} ≃* PCGroup smallGroup_32_{child} :=",
        f"  (CycExt.mulEquivOfRightInverseCardEq {stem}ToSource {forward}",
        f"    (by decide +kernel) ({card_proof})).symm",
    ])
    return lines


def cocycle_composition_alignment_lines(
        source_type, stem, result, child, source_exponents, standard_exponents):
    """Emit a cheap indexed equivalence to the standard representative for ``child``."""
    def exponent_permutation(exponents, label):
        permutation = []
        seen = set()
        for row in exponents:
            if len(row) != 5 or any(bit not in (0, 1) for bit in row):
                raise RuntimeError(f"malformed exponent row for {label}")
            target_index = sum(bit << index for index, bit in enumerate(row))
            if target_index in seen:
                raise RuntimeError(f"non-permutation exponent table for {label}")
            seen.add(target_index)
            permutation.append(target_index)
        if len(permutation) != 32 or seen != set(range(32)):
            raise RuntimeError(f"incomplete exponent table for {label}")
        return permutation

    source_to_pc = exponent_permutation(
        source_exponents, f"coverage SmallGroup(32,{child})"
    )
    standard_to_pc = exponent_permutation(
        standard_exponents, f"standard SmallGroup(32,{child})"
    )
    pc_to_standard = [None] * 32
    for standard_index, pc_index in enumerate(standard_to_pc):
        pc_to_standard[pc_index] = standard_index
    forward = [pc_to_standard[pc_index] for pc_index in source_to_pc]
    backward = [None] * 32
    for source_index, standard_index in enumerate(forward):
        if backward[standard_index] is not None:
            raise RuntimeError(f"non-bijective coverage map for SmallGroup(32,{child})")
        backward[standard_index] = source_index

    return [
        f"def {stem}ForwardIndex : Fin 32 → Fin 32 := {lean_vector(forward)}",
        f"def {stem}BackwardIndex : Fin 32 → Fin 32 := {lean_vector(backward)}",
        "",
        f"def {stem}ToGenerated (x : {source_type}) : generatedGroup{child} where",
        f"  fst := ((({stem}ForwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)",
        f"  snd := ⟨⟨({stem}ForwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩",
        "",
        f"def {stem}FromGenerated (x : generatedGroup{child}) : {source_type} where",
        f"  fst := ((({stem}BackwardIndex (certifiedExtensionIndex x)).val % 2 : ℕ) : ZMod 2)",
        f"  snd := ⟨⟨({stem}BackwardIndex (certifiedExtensionIndex x)).val / 2, by omega⟩⟩",
        "",
        "set_option maxHeartbeats 8000000 in",
        "-- Kernel reduction checks multiplication and both inverse tables.",
        f"noncomputable def {result} :",
        f"    {source_type} ≃* PCGroup smallGroup_32_{child} :=",
        f"  (CycExt.mulEquivOfExplicitInverse {stem}ToGenerated {stem}FromGenerated",
        "    (by decide +kernel) (by decide +kernel)).trans",
        f"    generatedGapEquiv{child}",
    ]


def relation_parent_alignment_lines(parent, exponents):
    """Emit a four-layer relation map for a certified group table of order 16."""
    inverse = [None] * 16
    for source_index, row in enumerate(exponents):
        target_index = sum(bit << index for index, bit in enumerate(row))
        if not 0 <= target_index < 16 or inverse[target_index] is not None:
            raise RuntimeError(f"non-permutation exponent table for SmallGroup(16,{parent})")
        inverse[target_index] = source_index
    if any(index is None for index in inverse):
        raise RuntimeError(f"incomplete exponent table for SmallGroup(16,{parent})")
    generator_preimages = [inverse[1 << index] for index in range(4)]
    layers = [f"sg16_{parent}_L{index}" for index in range(1, 5)]
    source_type = f"CertifiedTableGroup parent{parent}Table"
    stem = f"parent{parent}Relation"
    lines = [
        "-- The per-layer relation certificates require a larger kernel-reduction budget.",
        "set_option maxHeartbeats 8000000",
        "",
        f"def {stem}FromIndex (i : Fin 16) : {source_type} := ⟨i⟩",
        "",
        f"def {stem}Map0 : pcTower [] →* {source_type} where",
        "  toFun _ := 1",
        "  map_one' := rfl",
        "  map_mul' _ _ := (mul_one 1).symm",
        "",
    ]
    for depth in range(4, 1, -1):
        current = layers[depth - 1]
        rest = ", ".join(layers[depth:])
        rest_list = f"[{rest}]" if rest else "[]"
        tower = ", ".join(layers[depth - 1:])
        next_map = 0 if depth == 4 else depth + 1
        lines.extend([
            f"def {stem}Map{depth} : pcTower [{tower}] →* {source_type} :=",
            f"  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData {current} {rest_list})",
            f"    {stem}Map{next_map} ({stem}FromIndex {generator_preimages[depth - 1]})",
            "    (by decide +kernel)",
            "",
        ])
    rest = ", ".join(layers[1:])
    lines.extend([
        f"def {stem}ToSource : PCGroup smallGroup_16_{parent} →* {source_type} :=",
        f"  CycExt.liftOfGeneratorRelations (D := pcTowerLayerData {layers[0]} [{rest}])",
        f"    {stem}Map2 ({stem}FromIndex {generator_preimages[0]}) (by decide +kernel)",
        "",
        "set_option maxHeartbeats 8000000 in",
        "-- Kernel reduction checks the finite pc relations and explicit right inverse.",
        f"noncomputable def parent{parent}TableGapEquiv :",
        f"    {source_type} ≃* PCGroup smallGroup_16_{parent} :=",
        f"  (CycExt.mulEquivOfRightInverseCardEq {stem}ToSource parent{parent}TableToGap",
        "    (by decide +kernel) (by",
        f"      rw [card_smallGroup_16_{parent}, Nat.card_eq_fintype_card,",
        "        CertifiedTableGroup.fintype_card])).symm",
    ])
    return lines


OBSOLETE_CERTIFICATE_PATTERNS = [
    "CoverageLinearParent*ColumnsPart*.lean",
    "CoverageParent14ColumnsPart*.lean",
    "CoverageParent14OrbitPart*.lean",
    "CoverageParent14PackedColumnsPart*.lean",
    "CoverageOrbitParent14PathPart*.lean",
    "CoverageOrbitParent14Forest*.lean",
    "Parent14OrbitAlignmentPart*.lean",
]

OBSOLETE_CERTIFICATE_NAMES = [
    "CoverageLinearAll.lean",
    *(f"CoverageLinearParent{parent:02d}Identity.lean" for parent in range(1, 14)),
    "CoverageParent14Complete.lean",
    "CoverageParent14Data.lean",
    "CoverageParent14PackedData.lean",
    "CoverageLinearParent14BatchIdentity.lean",
    "CoverageOrbitParent14PathIdentity.lean",
    "CoverageOrbitParent14Decomposition.lean",
    "CoverageParent14Decomposition.lean",
    "CoverageParent14GapCore.lean",
    "CoverageParent14Identity.lean",
    "CoverageParent14Linear.lean",
    "CoverageParent14OrbitCore.lean",
    "CoverageParent14OrbitData.lean",
    "CoverageParent14OrbitIdentity.lean",
    "CoverageParent14PackedCore.lean",
    "CoverageParent14PackedIdentity.lean",
    "CoverageParent14ReductionEquiv.lean",
    "Parent14OrbitAlignment.lean",
]


def emit_parent14_structural_modules(output_dir: Path, header: str, group):
    """Keep only the seven representatives; completeness is a structural theorem."""
    if group["orbit_representatives"] != [0, 1, 2, 19, 20, 40, 184]:
        raise RuntimeError("Parent 14 normal-form coordinate certificates need updating")
    data = header + """import Smallgroups.UsefulTheorems.Order32Certificate.CocycleBasisParent14

/-! The seven representatives identified by structural quadratic classification. -/

namespace Smallgroups.UsefulTheorems.Order32Certificate

def orbitP14RepresentativeMask : Fin 7 → ℕ :=
  ![0, 1, 2, 19, 20, 40, 184]

end Smallgroups.UsefulTheorems.Order32Certificate
"""
    core = header + """import Smallgroups.UsefulTheorems.Order32Certificate.CoverageOrbitParent14Data
import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

def orbitP14SelectedCocycle (o : Fin 7) :=
  Order16Table.hCocycle parent14Table parent14HBasis
    (coeffMask 10 (orbitP14RepresentativeMask o))

theorem orbitP14SelectedCocycle_consistent (o : Fin 7) :
    IsCentralCocycle (orbitP14SelectedCocycle o) :=
  Order16Table.hCocycle_consistent parent14Table parent14HBasis
    orbitP14_hbasis_cocycle _

end Smallgroups.UsefulTheorems.Order32Certificate
"""
    reduction = header + """import Smallgroups.UsefulTheorems.Order32Certificate.Parent14QuadraticClassification

namespace Smallgroups.UsefulTheorems.Order32Certificate

open Smallgroups.UsefulTheorems.GF2Certificate

/-- Coverage now follows from the structural seven-form theorem. -/
theorem orbitP14_cocycle_orbit_complete
    (f : Order16Table.Q parent14Table → Order16Table.Q parent14Table → F2)
    (hf : IsCentralCocycle f) :
    ∃ o : Fin 7, Nonempty (CocycleGroup f hf ≃*
      CocycleGroup (orbitP14SelectedCocycle o) (orbitP14SelectedCocycle_consistent o)) :=
  parent14_extension_reduces_to_seven_structural f hf

end Smallgroups.UsefulTheorems.Order32Certificate
"""
    for suffix, content in (("Data", data), ("Core", core), ("Reduction", reduction)):
        (output_dir / f"CoverageOrbitParent14{suffix}.lean").write_text(content, encoding="utf-8")


def emit_lean_certificates(groups, output_dir: Path, chunk_size: int = 13):
    output_dir.mkdir(parents=True, exist_ok=True)
    for group in groups:
        build_orbit_forest(group)
    # The generated dependency graph records mathematical dependencies only.
    # Resource-sensitive serialization belongs in CI/build scheduling, not in
    # synthetic cross-parent imports that invalidate unrelated certificates.
    linear_parent_ids = [g["gap16_id"] for g in groups if g["gap16_id"] != 14]
    if not linear_parent_ids:
        raise RuntimeError("expected non-elementary-abelian order-16 parents")
    # Remove superseded pilot certificates.  Leaving these source files in the Lean
    # library makes Lake elaborate them even though the scalable orbit proof does not
    # import them, and on Windows their independent finite checks can exhaust memory.
    obsolete_patterns = OBSOLETE_CERTIFICATE_PATTERNS
    for pattern in obsolete_patterns:
        for path in output_dir.glob(pattern):
            path.unlink()
    obsolete_names = OBSOLETE_CERTIFICATE_NAMES
    for name in obsolete_names:
        path = output_dir / name
        if path.exists():
            path.unlink()
    header = """/-
Copyright (c) 2026 Smallgroups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Smallgroups contributors
-/
"""
    table_lines = [
        header.rstrip(),
        "import Smallgroups.UsefulTheorems.PGroupGeneration.CertifiedTable",
        "",
        "set_option maxRecDepth 100000",
        "set_option linter.style.longLine false",
        "",
        "/-! Generated from `Certificates/Order32/central_extensions.json`; do not edit. -/",
        "",
        "namespace Smallgroups.UsefulTheorems.Order32Certificate",
        "",
    ]
    for group in groups:
        parent = group["gap16_id"]
        rows = "![" + ", ".join(lean_vector(row) for row in group["mul"]) + "]"
        table_lines.extend([
            f"def parent{parent}Mul : Fin 16 → Fin 16 → Fin 16 := {rows}",
            f"def parent{parent}Inv : Fin 16 → Fin 16 := {lean_vector(group['inv'])}",
            f"def parent{parent}Table : CertifiedGroupTable 16 where",
            f"  mul := parent{parent}Mul",
            f"  inv := parent{parent}Inv",
            "  mul_assoc := by decide +kernel",
            "  zero_mul := by decide +kernel",
            "  mul_zero := by decide +kernel",
            "  inv_mul_cancel := by decide +kernel",
            "",
        ])
    table_lines.append("def order16ParentTable : Fin 14 → CertifiedGroupTable 16")
    for parent in range(1, 15):
        table_lines.append(f"  | {parent - 1} => parent{parent}Table")
    table_lines.append("")
    table_lines.extend(["end Smallgroups.UsefulTheorems.Order32Certificate", ""])
    (output_dir / "Tables.lean").write_text("\n".join(table_lines), encoding="utf-8")

    if all("pc_exponents" in group for group in groups):
        parent_alignment_parts = []
        for group in groups:
            parent = group["gap16_id"]
            part_name = f"ParentTableAlignmentPart{parent:02d}"
            parent_alignment_parts.append(part_name)
            exponents = "![" + ", ".join(
                "[" + ", ".join(map(str, row)) + "]" for row in group["pc_exponents"]
            ) + "]"
            lines = [
                header.rstrip(),
                "import Smallgroups.UsefulTheorems.Order32Certificate.Tables",
                "import Smallgroups.GAP.Polycyclic.Imported.Order16",
                "import Smallgroups.GAP.Polycyclic.PresentationHom",
            ]
            lines.extend([
                "",
                "set_option maxRecDepth 100000",
                "set_option linter.style.longLine false",
                "",
                f"/-! Checked table-to-PC alignment for `SmallGroup(16,{parent})`. -/",
                "",
                "namespace Smallgroups.UsefulTheorems.Order32Certificate",
                "",
                "open Smallgroups.GAP",
                "",
                f"def parent{parent}GapExponents : Fin 16 → List ℕ := {exponents}",
                f"def parent{parent}TableToGap (x : CertifiedTableGroup parent{parent}Table) :",
                f"    PCGroup smallGroup_16_{parent} :=",
                f"  evalVec (parent{parent}GapExponents x.val) (pcGens smallGroup_16_{parent}.layers)",
                "",
            ])
            lines.extend(relation_parent_alignment_lines(parent, group["pc_exponents"]))
            lines.extend(["", "end Smallgroups.UsefulTheorems.Order32Certificate", ""])
            (output_dir / f"{part_name}.lean").write_text("\n".join(lines), encoding="utf-8")
        parent_alignment = [header.rstrip()]
        parent_alignment.extend(
            f"import Smallgroups.UsefulTheorems.Order32Certificate.{name}"
            for name in parent_alignment_parts
        )
        parent_alignment.extend(["", "/-! All 14 order-16 table/PC alignments. -/", ""])
        (output_dir / "ParentTableAlignment.lean").write_text(
            "\n".join(parent_alignment), encoding="utf-8"
        )
        wild_to_gap = [14, 5, 8, 6, 7, 9, 1, 10, 11, 3, 13, 12, 4, 2]
        wild_alignment = [
            header.rstrip(),
            "import Smallgroups.UsefulTheorems.Order32Certificate.ParentTableAlignment",
            "import Smallgroups.GAP.Polycyclic.Imported.Order16Match",
            "",
            "/-! Alignment from each Wild order-16 representative to its certified table. -/",
            "",
            "namespace Smallgroups.UsefulTheorems.Order32Certificate",
            "",
            "open Smallgroups.GAP",
            "",
            "def wildParentGapIndex : Fin 14 → Fin 14",
        ]
        for wild, parent in enumerate(wild_to_gap):
            wild_alignment.append(f"  | {wild} => {parent - 1}")
        wild_alignment.extend([
            "",
            "noncomputable def wildParentTableEquiv : ∀ i : Fin 14,",
            "    CertifiedTableGroup (order16ParentTable (wildParentGapIndex i)) ≃*",
            "      order16_wild_reps i",
        ])
        for wild, parent in enumerate(wild_to_gap):
            wild_alignment.append(
                f"  | {wild} => parent{parent}TableGapEquiv.trans order16_{parent}_equiv"
            )
        wild_alignment.extend(["", "end Smallgroups.UsefulTheorems.Order32Certificate", ""])
        (output_dir / "ParentWildAlignment.lean").write_text(
            "\n".join(wild_alignment), encoding="utf-8"
        )

    # Check every H² basis vector once per parent.  Both the coverage proof and the
    # 51 standard representatives reuse these modules, so representative consistency
    # follows from linear closure instead of repeating a cubic cocycle enumeration.
    basis_module_by_parent = {}
    for group in groups:
        parent = group["gap16_id"]
        hdim_parent = group["h2_dimension"]
        linear_prefix = "parent14" if parent == 14 else f"coverageP{parent}"
        orbit_prefix = f"orbitP{parent}"
        module_name = f"CocycleBasisParent{parent:02d}"
        basis_module_by_parent[parent] = module_name
        basis = [
            header.rstrip(),
            "import Smallgroups.UsefulTheorems.Order32Certificate.Tables",
            "import Smallgroups.UsefulTheorems.PGroupGeneration.CocycleSynthesis",
            "",
            "set_option maxRecDepth 100000",
            "set_option linter.style.longLine false",
            "",
            f"/-! Kernel-checked H² basis cocycles for `SmallGroup(16,{parent})`. -/",
            "",
            "namespace Smallgroups.UsefulTheorems.Order32Certificate",
            "",
            "open Smallgroups.UsefulTheorems.GF2Certificate",
            "",
            f"def {linear_prefix}HBasis : Fin {hdim_parent} → ℕ := "
            f"{lean_vector(group['h2_basis'])}",
            "",
            f"theorem {orbit_prefix}_hbasis_cocycle (i : Fin {hdim_parent}) :",
            "    IsCentralCocycle",
            f"      (Order16Table.decodeTwo parent{parent}Table "
            f"(twoMask ({linear_prefix}HBasis i))) := by",
            ("  fin_cases i\n  decide +kernel"
             if hdim_parent == 1 else "  fin_cases i <;> decide +kernel"),
            "",
            "end Smallgroups.UsefulTheorems.Order32Certificate",
            "",
        ]
        (output_dir / f"{module_name}.lean").write_text(
            "\n".join(basis), encoding="utf-8"
        )

    def inverse_permutation(permutation):
        answer = [0] * len(permutation)
        for i, value in enumerate(permutation):
            answer[value] = i
        return answer

    # Non-elementary-abelian parents retain checked cohomology decomposition.
    # Parent 14 uses structural quadratic classification instead.
    all_coverage_identities = []
    for group in groups:
        parent = group["gap16_id"]
        if parent == 14:
            continue
        bdim = group["b2_dimension"]
        hdim_parent = group["h2_dimension"]
        total_dim = bdim + hdim_parent
        rank_parent = len(group["equation_triples"])
        prefix = f"coverageP{parent}"
        module_tag = f"CoverageLinearParent{parent:02d}"
        triples_parent = "![" + ", ".join(
            f"({a}, {b}, {c})" for a, b, c in group["equation_triples"]
        ) + "]"
        data = [
            header.rstrip(),
            "import Smallgroups.UsefulTheorems.Order32Certificate.Tables",
            f"import Smallgroups.UsefulTheorems.Order32Certificate."
            f"CocycleBasisParent{parent:02d}",
            "import Smallgroups.UsefulTheorems.PGroupGeneration.PackedCoverage",
            "",
            "set_option maxRecDepth 100000",
            "set_option linter.style.longLine false",
            "",
            f"/-! Generated packed linear coverage certificate for `SmallGroup(16,{parent})`. -/",
            "",
            "namespace Smallgroups.UsefulTheorems.Order32Certificate",
            "",
            "open Smallgroups.UsefulTheorems.GF2Certificate",
            "",
            f"def {prefix}BBasis : Fin {bdim} → ℕ := {lean_vector(group['b2_basis'])}",
            f"def {prefix}DBasis : Fin {bdim} → ℕ := {lean_vector(group['b2_preimages'])}",
            f"def {prefix}TotalBasis : Fin ({bdim} + {hdim_parent}) → ℕ :=",
            f"  Fin.append {prefix}BBasis {prefix}HBasis",
            f"def {prefix}CoordinateRows : Fin {total_dim} → ℕ :=",
            f"  {lean_vector(group['coordinate_rows'])}",
            f"def {prefix}EquationTriples : Fin {rank_parent} → Fin 16 × Fin 16 × Fin 16 :=",
            f"  {triples_parent}",
            f"def {prefix}CorrectionColumns : Fin {rank_parent} → ℕ :=",
            f"  {lean_vector(group['correction_columns'])}",
            f"def {prefix}PackedCoordinateMasks : Fin 225 → ℕ :=",
            f"  {lean_vector(group['coordinate_columns'])}",
            f"def {prefix}PackedEquationMasks : Fin 225 → ℕ :=",
            f"  {lean_vector(group['equation_columns'])}",
            "",
            f"def {prefix}ReductionMap : TwoVec →ₗ[F2] TwoVec :=",
            f"  (synthesizeTwo {prefix}TotalBasis).comp (analyzeTwo {prefix}CoordinateRows) +",
            f"    (synthesizeTwo {prefix}CorrectionColumns).comp",
            f"      (Order16Table.equationMap parent{parent}Table {prefix}EquationTriples)",
            "",
            "set_option maxHeartbeats 8000000 in",
            "-- Finite kernel check of the generated coboundary preimages.",
            f"theorem {prefix}_coboundary_basis :",
            f"    (Order16Table.coboundaryVec parent{parent}Table).comp",
            f"        (synthesizeOne {prefix}DBasis) = synthesizeTwo {prefix}BBasis := by",
            f"  apply (Pi.basisFun F2 (Fin {bdim})).ext",
            "  simp_rw [Pi.basisFun_apply]",
            "  decide +kernel",
            "",
            "end Smallgroups.UsefulTheorems.Order32Certificate",
            "",
        ]
        (output_dir / f"{module_tag}Data.lean").write_text(
            "\n".join(data), encoding="utf-8"
        )

        parent_parts = []
        for part_index, offset in enumerate(range(0, 225, 15), start=1):
            part_name = f"{module_tag}ColumnsPart{part_index:02d}"
            parent_parts.append(part_name)
            lines = [
                header.rstrip(),
                f"import Smallgroups.UsefulTheorems.Order32Certificate.{module_tag}Data",
                "",
                f"/-! Generated packed column checks for parent {parent}; do not edit. -/",
                "",
                "namespace Smallgroups.UsefulTheorems.Order32Certificate",
                "",
                "open Smallgroups.UsefulTheorems.GF2Certificate",
                "",
            ]
            for q in range(offset, min(offset + 15, 225)):
                i, j = divmod(q, 15)
                lines.extend([
                    f"theorem {prefix}_reduction_column_{i}_{j} :",
                    f"    {prefix}ReductionMap (unitTwo ({i}, {j})) = unitTwo ({i}, {j}) := by",
                    f"  unfold {prefix}ReductionMap",
                    f"  apply Order16Table.reductionColumnOfPacked parent{parent}Table",
                    f"      {prefix}TotalBasis {prefix}CoordinateRows {prefix}EquationTriples",
                    f"      {prefix}CorrectionColumns ({i}, {j})",
                    f"      ({prefix}PackedCoordinateMasks {q}) ({prefix}PackedEquationMasks {q})",
                    "  · decide +kernel",
                    "  · decide +kernel",
                    "  · decide +kernel",
                    "  · decide +kernel",
                    "",
                ])
            lines.extend(["end Smallgroups.UsefulTheorems.Order32Certificate", ""])
            (output_dir / f"{part_name}.lean").write_text(
                "\n".join(lines), encoding="utf-8"
            )

        identity_name = f"{module_tag}Identity"
        identity_parent = [header.rstrip()]
        identity_parent.extend(
            f"import Smallgroups.UsefulTheorems.Order32Certificate.{name}"
            for name in parent_parts
        )
        identity_parent.extend([
            "",
            "namespace Smallgroups.UsefulTheorems.Order32Certificate",
            "",
            "open Smallgroups.UsefulTheorems.GF2Certificate",
            "",
            f"theorem {prefix}_reduction_on_unit : ∀ p : TwoIndex,",
            f"    {prefix}ReductionMap (unitTwo p) = unitTwo p",
        ])
        for q in range(225):
            i, j = divmod(q, 15)
            identity_parent.append(
                f"  | ({i}, {j}) => {prefix}_reduction_column_{i}_{j}"
            )
        identity_parent.extend([
            "",
            f"theorem {prefix}_reduction_identity : {prefix}ReductionMap = LinearMap.id := by",
            "  apply (Pi.basisFun F2 TwoIndex).ext",
            "  intro p",
            "  rw [basisFun_eq_unitTwo]",
            f"  exact {prefix}_reduction_on_unit p",
            "",
            "end Smallgroups.UsefulTheorems.Order32Certificate",
            "",
        ])
        (output_dir / f"{identity_name}.lean").write_text(
            "\n".join(identity_parent), encoding="utf-8"
        )

        batch_name = f"{module_tag}BatchIdentity"
        all_coverage_identities.append(batch_name)
        batch = [
            header.rstrip(),
            f"import Smallgroups.UsefulTheorems.Order32Certificate.{module_tag}Data",
            "",
            "set_option maxRecDepth 100000",
            "",
            f"/-! One batched kernel check of all 225 reduction columns for parent {parent}. -/",
            "",
            "namespace Smallgroups.UsefulTheorems.Order32Certificate",
            "",
            "open Smallgroups.UsefulTheorems.GF2Certificate",
            "",
            "set_option maxHeartbeats 100000000 in",
            "-- The proposition contains only finite bit-vector computations.",
            f"theorem {prefix}_packed_certificate :",
            f"    Order16Table.PackedCoverageCertificate parent{parent}Table",
            f"      {prefix}TotalBasis {prefix}CoordinateRows {prefix}EquationTriples",
            f"      {prefix}CorrectionColumns {prefix}PackedCoordinateMasks",
            f"      {prefix}PackedEquationMasks := by",
            "  unfold Order16Table.PackedCoverageCertificate",
            "  decide +kernel",
            "",
            f"theorem {prefix}_reduction_identity_batched : {prefix}ReductionMap = LinearMap.id := by",
            f"  unfold {prefix}ReductionMap",
            f"  exact Order16Table.reductionIdentityOfPackedCertificate parent{parent}Table",
            f"    {prefix}TotalBasis {prefix}CoordinateRows {prefix}EquationTriples",
            f"    {prefix}CorrectionColumns {prefix}PackedCoordinateMasks",
            f"    {prefix}PackedEquationMasks {prefix}_packed_certificate",
            "",
            "end Smallgroups.UsefulTheorems.Order32Certificate",
            "",
        ]
        (output_dir / f"{batch_name}.lean").write_text(
            "\n".join(batch), encoding="utf-8"
        )

    all_coverage = [header.rstrip()]
    all_coverage.extend(
        f"import Smallgroups.UsefulTheorems.Order32Certificate.{name}"
        for name in all_coverage_identities
    )
    all_coverage.extend(["", "/-! Packed linear coverage for all 14 order-16 parents. -/", ""])
    (output_dir / "CoverageLinearAll.lean").write_text(
        "\n".join(all_coverage), encoding="utf-8"
    )

    # Scalable orbit certificates for parents 1--13.  Instead of checking one
    # full automorphism/coboundary witness for every H² vector, Lean checks the
    # action and correction on each H² basis vector for each automorphism
    # generator.  Arbitrary orbit paths are then composed by the generic
    # `OrbitReduction` theorem.
    canonical_occurrence = {}
    canonical_extension_by_child = {}
    for canonical_group in groups:
        for canonical_extension in canonical_group["extensions"]:
            canonical_occurrence.setdefault(
                canonical_extension["gap32_id"],
                (canonical_group["gap16_id"], canonical_extension["orbit_index"]),
            )
            canonical_extension_by_child.setdefault(
                canonical_extension["gap32_id"], canonical_extension
            )

    scalable_complete_modules = []
    for group in groups:
        parent = group["gap16_id"]
        h = group["h2_dimension"]
        vector_count = 2 ** h
        orbit_count = len(group["orbit_representatives"])
        aut_count = len(group["aut_generators"])
        prefix = f"orbitP{parent}"
        linear_prefix = "parent14" if parent == 14 else f"coverageP{parent}"
        linear_module = (
            "CoverageParent14" if parent == 14 else f"CoverageLinearParent{parent:02d}"
        )
        linear_identity_module = (
            "CoverageLinearParent14BatchIdentity"
            if parent == 14 else f"CoverageLinearParent{parent:02d}BatchIdentity"
        )
        linear_identity_theorem = (
            "parent14_reduction_identity_batched"
            if parent == 14 else f"{linear_prefix}_reduction_identity_batched"
        )
        module_tag = f"CoverageOrbitParent{parent:02d}"

        if parent == 14:
            emit_parent14_structural_modules(output_dir, header, group)
        else:
            def lean_nested_vectors(rows):
                return "![" + ", ".join(lean_vector(row) for row in rows) + "]"

            def lean_path(word):
                return "[" + ", ".join(str(x) for x in word) + "]"

            aut_inverses = [inverse_permutation(p) for p in group["aut_generators"]]
            data = [
                header.rstrip(),
                f"import Smallgroups.UsefulTheorems.Order32Certificate.{linear_module}Data",
                "import Smallgroups.UsefulTheorems.PGroupGeneration.OrbitReduction",
                "",
                "set_option maxRecDepth 100000",
                "set_option linter.style.longLine false",
                "",
                f"/-! Generated compositional orbit data for `SmallGroup(16,{parent})`. -/",
                "",
                "namespace Smallgroups.UsefulTheorems.Order32Certificate",
                "",
                "open Smallgroups.UsefulTheorems.GF2Certificate",
                "",
                f"def {prefix}RepresentativeMask : Fin {orbit_count} → ℕ :=",
                f"  {lean_vector(group['orbit_representatives'])}",
                f"def {prefix}Index : Fin {vector_count} → Fin {orbit_count} :=",
                f"  {lean_vector([n['orbit_index'] for n in group['orbit_normalizations']])}",
                f"def {prefix}AutPerm : Fin {aut_count} → Fin 16 → Fin 16 :=",
                f"  {lean_nested_vectors(group['aut_generators'])}",
                f"def {prefix}AutInvPerm : Fin {aut_count} → Fin 16 → Fin 16 :=",
                f"  {lean_nested_vectors(aut_inverses)}",
                f"def {prefix}ActionColumns : Fin {aut_count} → Fin {h} → ℕ :=",
                f"  {lean_nested_vectors(group['h2_action_generators'])}",
                f"def {prefix}CorrectionColumns : Fin {aut_count} → Fin {h} → ℕ :=",
                f"  {lean_nested_vectors(group['h2_action_correction_generators'])}",
            ]
            data.extend([
                "",
                f"def {prefix}RepresentativeCoeff (k : Fin {vector_count}) : Fin {h} → F2 :=",
                f"  coeffMask {h} ({prefix}RepresentativeMask ({prefix}Index k))",
                f"def {prefix}TargetCoeff (k : Fin {vector_count}) : Fin {h} → F2 :=",
                f"  coeffMask {h} k.val",
            ])
            data.extend([
                "",
                "end Smallgroups.UsefulTheorems.Order32Certificate",
                "",
            ])
            (output_dir / f"{module_tag}Data.lean").write_text(
                "\n".join(data), encoding="utf-8"
            )

            core = [
                header.rstrip(),
                f"import Smallgroups.UsefulTheorems.Order32Certificate.{module_tag}Data",
            ]
            core.extend([
                "",
                "set_option maxRecDepth 100000",
                "set_option linter.style.longLine false",
                "",
                f"/-! Kernel-checked generator action for parent {parent}. -/",
                "",
                "namespace Smallgroups.UsefulTheorems.Order32Certificate",
                "",
                "open Smallgroups.UsefulTheorems.GF2Certificate",
                "",
                f"def {prefix}AutCertificate (g : Fin {aut_count}) : Prop :=",
                f"  (∀ a : Fin 16, {prefix}AutInvPerm g ({prefix}AutPerm g a) = a) ∧",
                f"  (∀ a : Fin 16, {prefix}AutPerm g ({prefix}AutInvPerm g a) = a) ∧",
                f"  (∀ a b : Fin 16, {prefix}AutPerm g (parent{parent}Table.mul a b) =",
                f"    parent{parent}Table.mul ({prefix}AutPerm g a) ({prefix}AutPerm g b))",
                "",
                f"theorem {prefix}_aut_certificate : ∀ g : Fin {aut_count}, {prefix}AutCertificate g := by",
                "  intro g",
                f"  fin_cases g <;> unfold {prefix}AutCertificate <;> decide +kernel",
                "",
                f"def {prefix}Aut (g : Fin {aut_count}) :",
                f"    Order16Table.Q parent{parent}Table ≃* Order16Table.Q parent{parent}Table where",
                f"  toFun x := ⟨{prefix}AutPerm g x.val⟩",
                f"  invFun x := ⟨{prefix}AutInvPerm g x.val⟩",
                "  left_inv x := by",
                "    apply CertifiedTableGroup.ext",
                f"    exact ({prefix}_aut_certificate g).1 x.val",
                "  right_inv x := by",
                "    apply CertifiedTableGroup.ext",
                f"    exact ({prefix}_aut_certificate g).2.1 x.val",
                "  map_mul' x y := by",
                "    apply CertifiedTableGroup.ext",
                f"    exact ({prefix}_aut_certificate g).2.2 x.val y.val",
                "",
                f"set_option maxHeartbeats 8000000 in",
                "-- Each column check establishes the action and coboundary correction on one H² basis vector.",
                f"theorem {prefix}_action_linear (g : Fin {aut_count}) :",
                f"    (Order16Table.precomposeTwoLinear parent{parent}Table ({prefix}Aut g)).comp",
                f"        ((Order16Table.decodeTwoLinear parent{parent}Table).comp",
                f"          (synthesizeTwo {linear_prefix}HBasis)) =",
                f"      (Order16Table.centralCoboundaryLinear parent{parent}Table).comp",
                f"          (Order16Table.orbitCorrection parent{parent}Table",
                f"            ({prefix}CorrectionColumns g)) +",
                f"        (Order16Table.decodeTwoLinear parent{parent}Table).comp",
                f"          ((synthesizeTwo {linear_prefix}HBasis).comp",
                f"            (Order16Table.orbitAction ({prefix}ActionColumns g))) := by",
                f"  apply (Pi.basisFun F2 (Fin {h})).ext",
                "  simp_rw [Pi.basisFun_apply]",
                "  intro i",
                "  ext a b",
                "  fin_cases g <;> fin_cases i <;> decide +kernel +revert",
                "",
                f"def {prefix}SelectedCocycle (o : Fin {orbit_count}) :=",
                f"  Order16Table.hCocycle parent{parent}Table {linear_prefix}HBasis",
                f"    (coeffMask {h} ({prefix}RepresentativeMask o))",
                f"theorem {prefix}SelectedCocycle_consistent (o : Fin {orbit_count}) :",
                f"    IsCentralCocycle ({prefix}SelectedCocycle o) :=",
                f"  Order16Table.hCocycle_consistent parent{parent}Table {linear_prefix}HBasis",
                f"    {prefix}_hbasis_cocycle _",
                "",
                f"def {prefix}TargetCocycle (k : Fin {vector_count}) :=",
                f"  Order16Table.hCocycle parent{parent}Table {linear_prefix}HBasis ({prefix}TargetCoeff k)",
                f"theorem {prefix}TargetCocycle_consistent (k : Fin {vector_count}) :",
                f"    IsCentralCocycle ({prefix}TargetCocycle k) :=",
                f"  Order16Table.hCocycle_consistent parent{parent}Table {linear_prefix}HBasis",
                f"    {prefix}_hbasis_cocycle _",
                "",
                "end Smallgroups.UsefulTheorems.Order32Certificate",
                "",
            ])
            (output_dir / f"{module_tag}Core.lean").write_text(
                "\n".join(core), encoding="utf-8"
            )
            path_identity_name = f"{module_tag}PathIdentity"
            if parent != 14:
                path_parts = []
                path_chunk_size = 16
                for part_index, offset in enumerate(range(0, vector_count, path_chunk_size), start=1):
                    part_name = f"{module_tag}PathPart{part_index:02d}"
                    path_parts.append(part_name)
                    lines = [
                        header.rstrip(),
                        f"import Smallgroups.UsefulTheorems.Order32Certificate.{module_tag}Core",
                    ]
                    lines.extend([
                        "",
                        "set_option maxRecDepth 100000",
                        *( ["set_option linter.style.longLine false"] if parent == 14 else [] ),
                        "",
                        f"/-! Checked short orbit paths for parent {parent}; generated part {part_index}. -/",
                        "",
                        "namespace Smallgroups.UsefulTheorems.Order32Certificate",
                        "",
                        "open Smallgroups.UsefulTheorems.GF2Certificate",
                        "",
                    ])
                    for k in range(offset, min(offset + path_chunk_size, vector_count)):
                        word_term = lean_path(group["orbit_words"][k])
                        lines.extend([
                            f"theorem {prefix}_path_endpoint_{k} :",
                            f"    Order16Table.applyOrbitPath {prefix}ActionColumns {word_term}",
                            f"      ({prefix}RepresentativeCoeff {k}) = {prefix}TargetCoeff {k} := by",
                            "  decide +kernel",
                            "",
                            f"noncomputable def {prefix}NormalizeEquiv{k} :",
                            f"    CocycleGroup ({prefix}SelectedCocycle ({prefix}Index {k}))",
                            f"        ({prefix}SelectedCocycle_consistent ({prefix}Index {k})) ≃*",
                            f"      CocycleGroup ({prefix}TargetCocycle {k})",
                            f"        ({prefix}TargetCocycle_consistent {k}) := by",
                            f"  let e := Order16Table.orbitPathEquiv parent{parent}Table {linear_prefix}HBasis",
                            f"    {prefix}ActionColumns {prefix}CorrectionColumns {prefix}_hbasis_cocycle",
                            f"    {prefix}Aut {prefix}_action_linear {word_term} ({prefix}RepresentativeCoeff {k})",
                            "  exact e.trans (Order16Table.CocycleGroup.congrCocycleEq _ _",
                            f"    (congrArg (Order16Table.hCocycle parent{parent}Table {linear_prefix}HBasis)",
                            f"      {prefix}_path_endpoint_{k}))",
                            "",
                        ])
                    lines.extend(["end Smallgroups.UsefulTheorems.Order32Certificate", ""])
                    (output_dir / f"{part_name}.lean").write_text("\n".join(lines), encoding="utf-8")

            if parent != 14:
                path_identity = [header.rstrip()]
                path_identity.extend(
                    f"import Smallgroups.UsefulTheorems.Order32Certificate.{name}"
                    for name in path_parts
                )
                path_identity.extend([
                "",
                "namespace Smallgroups.UsefulTheorems.Order32Certificate",
                "",
                ])
                if vector_count < 16:
                    path_identity.extend([
                    f"noncomputable def {prefix}NormalizeEquiv : ∀ k : Fin {vector_count},",
                    f"    CocycleGroup ({prefix}SelectedCocycle ({prefix}Index k))",
                    f"        ({prefix}SelectedCocycle_consistent ({prefix}Index k)) ≃*",
                    f"      CocycleGroup ({prefix}TargetCocycle k) ({prefix}TargetCocycle_consistent k)",
                    ])
                    for k in range(vector_count):
                        path_identity.append(f"  | {k} => {prefix}NormalizeEquiv{k}")
                else:
                # Lean's numeral-pattern exhaustiveness checker stops unfolding `Fin`
                # after fifteen successors.  A finite-cases existence proof followed by
                # choice scales to the 1024 parent-14 coefficient vectors.
                    path_identity.extend([
                    "set_option maxRecDepth 100000 in",
                    "set_option maxHeartbeats 8000000 in",
                    "-- Enumerating every finite coefficient vector selects its checked normalization equivalence.",
                    f"theorem {prefix}NormalizeEquiv_nonempty (k : Fin {vector_count}) : Nonempty (",
                    f"    CocycleGroup ({prefix}SelectedCocycle ({prefix}Index k))",
                    f"        ({prefix}SelectedCocycle_consistent ({prefix}Index k)) ≃*",
                    f"      CocycleGroup ({prefix}TargetCocycle k) ({prefix}TargetCocycle_consistent k)) := by",
                    "  fin_cases k",
                    ])
                    for k in range(vector_count):
                        path_identity.append(f"  · exact ⟨{prefix}NormalizeEquiv{k}⟩")
                    path_identity.extend([
                    "",
                    f"noncomputable def {prefix}NormalizeEquiv (k : Fin {vector_count}) :",
                    f"    CocycleGroup ({prefix}SelectedCocycle ({prefix}Index k))",
                    f"        ({prefix}SelectedCocycle_consistent ({prefix}Index k)) ≃*",
                    f"      CocycleGroup ({prefix}TargetCocycle k) ({prefix}TargetCocycle_consistent k) :=",
                    f"  ({prefix}NormalizeEquiv_nonempty k).some",
                    ])
                path_identity.extend(["", "end Smallgroups.UsefulTheorems.Order32Certificate", ""])
                (output_dir / f"{path_identity_name}.lean").write_text(
                    "\n".join(path_identity), encoding="utf-8"
                )

            decomposition = [
                header.rstrip(),
                f"import Smallgroups.UsefulTheorems.Order32Certificate.{linear_identity_module}",
                "import Smallgroups.UsefulTheorems.PGroupGeneration.CohomologyDecomposition",
                "",
                "namespace Smallgroups.UsefulTheorems.Order32Certificate",
                "",
                "open Smallgroups.UsefulTheorems.GF2Certificate",
                "",
                f"theorem {prefix}_decompose_cocycle (v : TwoVec)",
                f"    (hv : IsCentralCocycle (Order16Table.decodeTwo parent{parent}Table v)) :",
                f"    ∃ d : OneVec, ∃ q : Fin {h} → F2,",
                f"      v = Order16Table.coboundaryVec parent{parent}Table d +",
                f"        synthesizeTwo {linear_prefix}HBasis q := by",
                f"  apply Order16Table.decomposeCocycle parent{parent}Table {linear_prefix}BBasis",
                f"    {linear_prefix}DBasis {linear_prefix}HBasis {linear_prefix}CoordinateRows",
                f"    {linear_prefix}EquationTriples {linear_prefix}CorrectionColumns",
                f"  · simpa [{linear_prefix}ReductionMap, {linear_prefix}TotalBasis] using",
                f"      {linear_identity_theorem}",
                f"  · exact {linear_prefix}_coboundary_basis",
                "  · exact hv",
                "",
                "end Smallgroups.UsefulTheorems.Order32Certificate",
                "",
            ]
            (output_dir / f"{module_tag}Decomposition.lean").write_text(
                "\n".join(decomposition), encoding="utf-8"
            )

            reduction = [
                header.rstrip(),
                f"import Smallgroups.UsefulTheorems.Order32Certificate.{module_tag}Core",
                f"import Smallgroups.UsefulTheorems.Order32Certificate.{path_identity_name}",
                f"import Smallgroups.UsefulTheorems.Order32Certificate.{module_tag}Decomposition",
                "",
                "namespace Smallgroups.UsefulTheorems.Order32Certificate",
                "",
                "open Smallgroups.UsefulTheorems.GF2Certificate",
                "",
                f"def {prefix}HCocycle (c : Fin {h} → F2) :=",
                f"  Order16Table.hCocycle parent{parent}Table {linear_prefix}HBasis c",
                f"theorem {prefix}HCocycle_consistent (c : Fin {h} → F2) :",
                f"    IsCentralCocycle ({prefix}HCocycle c) :=",
                f"  Order16Table.hCocycle_consistent parent{parent}Table {linear_prefix}HBasis",
                f"    {prefix}_hbasis_cocycle c",
                "",
                f"theorem {prefix}_cocycle_reduces_to_H",
                f"    (f : Order16Table.Q parent{parent}Table → Order16Table.Q parent{parent}Table → F2)",
                "    (hf : IsCentralCocycle f) :",
                f"    ∃ c : Fin {h} → F2, Nonempty (CocycleGroup f hf ≃*",
                f"      CocycleGroup ({prefix}HCocycle c) ({prefix}HCocycle_consistent c)) := by",
                f"  let v := Order16Table.encodeTwo parent{parent}Table f",
                f"  have hvdecode : Order16Table.decodeTwo parent{parent}Table v = f :=",
                f"    Order16Table.decodeTwo_encodeTwo parent{parent}Table hf",
                f"  have hv : IsCentralCocycle (Order16Table.decodeTwo parent{parent}Table v) := by",
                "    rw [hvdecode]",
                "    exact hf",
                f"  obtain ⟨d, c, hdecomp⟩ := {prefix}_decompose_cocycle v hv",
                f"  let cochain := Order16Table.decodeOne parent{parent}Table d",
                f"  have hcochain : cochain 1 = 0 := Order16Table.decodeOne_zero parent{parent}Table d",
                f"  have hshift : f = addCoboundary ({prefix}HCocycle c) cochain := by",
                "    funext a b",
                "    calc",
                f"      f a b = Order16Table.decodeTwo parent{parent}Table v a b := by rw [hvdecode]",
                f"      _ = Order16Table.decodeTwo parent{parent}Table",
                f"          (Order16Table.coboundaryVec parent{parent}Table d +",
                f"            synthesizeTwo {linear_prefix}HBasis c) a b := by rw [hdecomp]",
                f"      _ = Order16Table.decodeTwo parent{parent}Table",
                f"            (Order16Table.coboundaryVec parent{parent}Table d) a b +",
                f"          Order16Table.decodeTwo parent{parent}Table",
                f"            (synthesizeTwo {linear_prefix}HBasis c) a b :=",
                "            Order16Table.decodeTwo_add _ _ _ _ _",
                f"      _ = centralCoboundary (Order16Table.Q parent{parent}Table) F2 cochain a b +",
                f"          {prefix}HCocycle c a b := by",
                "            rw [Order16Table.decodeTwo_coboundaryVec]",
                "            rfl",
                f"      _ = addCoboundary ({prefix}HCocycle c) cochain a b := by",
                "            simp [addCoboundary, centralCoboundary]",
                "            abel",
                "  refine ⟨c, ⟨?_⟩⟩",
                "  exact (Order16Table.CocycleGroup.congrCocycleEq hf",
                f"    (({prefix}HCocycle_consistent c).addCoboundary cochain hcochain) hshift).trans",
                f"      (CocycleGroup.coboundaryEquiv ({prefix}HCocycle_consistent c) cochain hcochain)",
                "",
                f"set_option maxHeartbeats 8000000 in",
                "-- Exhaustive bit decoding verifies coefficient lookup for every H² vector.",
                f"theorem {prefix}_coeffMask_vecIndex : ∀ (c : Fin {h} → F2) (i : Fin {h}),",
                f"    coeffMask {h} (vecIndex {h} c).val i = c i := by",
                "  decide +kernel",
                "",
                f"theorem {prefix}_cocycle_orbit_complete",
                f"    (f : Order16Table.Q parent{parent}Table → Order16Table.Q parent{parent}Table → F2)",
                "    (hf : IsCentralCocycle f) :",
                f"    ∃ o : Fin {orbit_count}, Nonempty (CocycleGroup f hf ≃*",
                f"      CocycleGroup ({prefix}SelectedCocycle o) ({prefix}SelectedCocycle_consistent o)) := by",
                f"  obtain ⟨c, ⟨e⟩⟩ := {prefix}_cocycle_reduces_to_H f hf",
                f"  let k : Fin {vector_count} := vecIndex {h} c",
                f"  have hcoeff : {prefix}TargetCoeff k = c := by",
                "    funext i",
                f"    exact {prefix}_coeffMask_vecIndex c i",
                f"  have hcocycle : {prefix}TargetCocycle k = {prefix}HCocycle c := by",
                f"    exact congrArg (Order16Table.hCocycle parent{parent}Table {linear_prefix}HBasis) hcoeff",
                f"  refine ⟨{prefix}Index k, ⟨e.trans ?_⟩⟩",
                "  exact (Order16Table.CocycleGroup.congrCocycleEq _ _ hcocycle.symm).trans",
                f"    ({prefix}NormalizeEquiv k).symm",
                "",
                "end Smallgroups.UsefulTheorems.Order32Certificate",
                "",
            ]
            (output_dir / f"{module_tag}Reduction.lean").write_text(
                "\n".join(reduction), encoding="utf-8"
            )

        alignment_parts = []
        for extension in sorted(group["extensions"], key=lambda e: e["orbit_index"]):
            orbit_index = extension["orbit_index"]
            child = extension["gap32_id"]
            alignment_name = f"{module_tag}AlignmentPart{orbit_index + 1:02d}"
            alignment_parts.append(alignment_name)
            canonical_parent, canonical_orbit = canonical_occurrence[child]
            is_canonical = canonical_parent == parent and canonical_orbit == orbit_index
            indexed_composition_alignment = parent == 14 or not is_canonical
            lines = [header.rstrip()]
            if indexed_composition_alignment:
                lines.extend([
                    f"import Smallgroups.UsefulTheorems.Order32Certificate.{module_tag}Core",
                    f"import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart{child:02d}",
                ])
                lines.append("import Smallgroups.GAP.Polycyclic.PresentationHom")
            elif is_canonical:
                lines.extend([
                    f"import Smallgroups.UsefulTheorems.Order32Certificate.{module_tag}Core",
                    f"import Smallgroups.UsefulTheorems.Order32Certificate.AlignmentPart{child:02d}",
                ])
            lines.extend([
                "",
                "set_option maxRecDepth 100000",
                "set_option linter.style.longLine false",
                "",
                f"/-! Parent {parent}, orbit {orbit_index}, alignment to GAP id {child}. -/",
                "",
                "namespace Smallgroups.UsefulTheorems.Order32Certificate",
                "",
                "open Smallgroups.UsefulTheorems.GF2Certificate",
                "open Smallgroups.GAP",
                "",
                f"abbrev {prefix}OrbitGroup{orbit_index} := CocycleGroup",
                f"  ({prefix}SelectedCocycle {orbit_index}) ({prefix}SelectedCocycle_consistent {orbit_index})",
            ])
            if is_canonical and not indexed_composition_alignment:
                lines.extend([
                    f"set_option maxHeartbeats 8000000 in",
                    "-- Kernel check that this selected orbit is the canonical generated representative.",
                    f"noncomputable def {prefix}GapEquiv{orbit_index} :",
                    f"    {prefix}OrbitGroup{orbit_index} ≃* PCGroup smallGroup_32_{child} :=",
                    f"  (Order16Table.CocycleGroup.congrCocycleEq _ _ (by decide +kernel)).trans",
                    f"    generatedGapEquiv{child}",
                ])
            else:
                lines.extend(cocycle_composition_alignment_lines(
                    f"{prefix}OrbitGroup{orbit_index}",
                    f"{prefix}Standard{orbit_index}",
                    f"{prefix}GapEquiv{orbit_index}",
                    child,
                    extension["pc_exponents"],
                    canonical_extension_by_child[child]["pc_exponents"],
                ))
            lines.extend(["", "end Smallgroups.UsefulTheorems.Order32Certificate", ""])
            (output_dir / f"{alignment_name}.lean").write_text(
                "\n".join(lines), encoding="utf-8"
            )

        gap_core = [header.rstrip()]
        gap_core.extend(
            f"import Smallgroups.UsefulTheorems.Order32Certificate.{name}"
            for name in alignment_parts
        )
        gap_core.extend([
            "import Smallgroups.GAP.Order32",
            "",
            "namespace Smallgroups.UsefulTheorems.Order32Certificate",
            "",
            "open Smallgroups.GAP",
            "",
            f"def {prefix}GapIndex : Fin {orbit_count} → Fin 51 :=",
            f"  {lean_vector([e['gap32_id'] - 1 for e in sorted(group['extensions'], key=lambda e: e['orbit_index'])])}",
        ])
        if orbit_count < 16:
            gap_core.extend([
                f"noncomputable def {prefix}SelectedGapEquiv : ∀ o : Fin {orbit_count},",
                f"    CocycleGroup ({prefix}SelectedCocycle o) ({prefix}SelectedCocycle_consistent o) ≃*",
                f"      smallGroup32 ({prefix}GapIndex o)",
            ])
            for extension in sorted(group["extensions"], key=lambda e: e["orbit_index"]):
                orbit_index = extension["orbit_index"]
                gap_core.append(f"  | {orbit_index} => {prefix}GapEquiv{orbit_index}")
        else:
            gap_core.extend([
                f"theorem {prefix}SelectedGapEquiv_nonempty (o : Fin {orbit_count}) : Nonempty (",
                f"    CocycleGroup ({prefix}SelectedCocycle o) ({prefix}SelectedCocycle_consistent o) ≃*",
                f"      smallGroup32 ({prefix}GapIndex o)) := by",
                "  fin_cases o",
            ])
            for extension in sorted(group["extensions"], key=lambda e: e["orbit_index"]):
                orbit_index = extension["orbit_index"]
                gap_core.append(f"  · exact ⟨{prefix}GapEquiv{orbit_index}⟩")
            gap_core.extend([
                "",
                f"noncomputable def {prefix}SelectedGapEquiv (o : Fin {orbit_count}) :",
                f"    CocycleGroup ({prefix}SelectedCocycle o) ({prefix}SelectedCocycle_consistent o) ≃*",
                f"      smallGroup32 ({prefix}GapIndex o) :=",
                f"  ({prefix}SelectedGapEquiv_nonempty o).some",
            ])
        gap_core.extend(["", "end Smallgroups.UsefulTheorems.Order32Certificate", ""])
        (output_dir / f"{module_tag}GapCore.lean").write_text(
            "\n".join(gap_core), encoding="utf-8"
        )

        complete_name = f"{module_tag}Complete"
        scalable_complete_modules.append(complete_name)
        complete = [
            header.rstrip(),
            f"import Smallgroups.UsefulTheorems.Order32Certificate.{module_tag}Reduction",
            f"import Smallgroups.UsefulTheorems.Order32Certificate.{module_tag}GapCore",
            "",
            "namespace Smallgroups.UsefulTheorems.Order32Certificate",
            "",
            "open Smallgroups.UsefulTheorems.GF2Certificate",
            "open Smallgroups.GAP",
            "",
            f"theorem {prefix}_cocycle_gap_complete",
            f"    (f : Order16Table.Q parent{parent}Table → Order16Table.Q parent{parent}Table → F2)",
            "    (hf : IsCentralCocycle f) :",
            "    ∃ j : Fin 51, Nonempty (CocycleGroup f hf ≃* smallGroup32 j) := by",
            f"  obtain ⟨o, ⟨e⟩⟩ := {prefix}_cocycle_orbit_complete f hf",
            f"  exact ⟨{prefix}GapIndex o, ⟨e.trans ({prefix}SelectedGapEquiv o)⟩⟩",
            "",
            "end Smallgroups.UsefulTheorems.Order32Certificate",
            "",
        ]
        (output_dir / f"{complete_name}.lean").write_text(
            "\n".join(complete), encoding="utf-8"
        )

    scalable_all = [header.rstrip()]
    scalable_all.extend(
        f"import Smallgroups.UsefulTheorems.Order32Certificate.{name}"
        for name in scalable_complete_modules
    )
    scalable_all.extend([
        "",
        "/-! End-to-end cocycle coverage for all order-16 parent tables. -/",
        "",
        "namespace Smallgroups.UsefulTheorems.Order32Certificate",
        "",
        "open Smallgroups.UsefulTheorems.GF2Certificate",
        "open Smallgroups.GAP",
        "",
        "theorem order16ParentTable_cocycle_gap_complete : ∀ (p : Fin 14)",
        "    (f : Order16Table.Q (order16ParentTable p) →",
        "      Order16Table.Q (order16ParentTable p) → F2)",
        "    (hf : IsCentralCocycle f),",
        "    ∃ j : Fin 51, Nonempty (CocycleGroup f hf ≃* smallGroup32 j)",
    ])
    for parent in range(1, 15):
        scalable_all.append(
            f"  | {parent - 1}, f, hf => orbitP{parent}_cocycle_gap_complete f hf"
        )
    scalable_all.extend([
        "",
        "end Smallgroups.UsefulTheorems.Order32Certificate",
        "",
    ])
    (output_dir / "CoverageOrbitScalableAll.lean").write_text(
        "\n".join(scalable_all), encoding="utf-8"
    )

    canonical = {}
    for group in groups:
        for extension in group["extensions"]:
            canonical.setdefault(extension["gap32_id"], (group, extension))
    if sorted(canonical) != list(range(1, 52)):
        raise RuntimeError("canonical extensions do not cover GAP ids 1..51")

    part_names = []
    items = sorted(canonical.items())
    for part_index, offset in enumerate(range(0, len(items), chunk_size), start=1):
        part_name = f"RepsPart{part_index:02d}"
        part_names.append(part_name)
        lines = [
            header.rstrip(),
            "import Smallgroups.UsefulTheorems.Order32Certificate.Tables",
        ]
        part_parents = sorted({group["gap16_id"]
                               for _, (group, _) in items[offset:offset + chunk_size]})
        lines.extend(
            f"import Smallgroups.UsefulTheorems.Order32Certificate.{basis_module_by_parent[parent]}"
            for parent in part_parents
        )
        lines.extend([
            "",
            "set_option maxRecDepth 100000",
            "set_option linter.style.longLine false",
            "",
            "/-! Generated kernel-checkable central extensions; do not edit. -/",
            "",
            "namespace Smallgroups.UsefulTheorems.Order32Certificate",
            "",
            "open Smallgroups.UsefulTheorems.GF2Certificate",
            "",
        ])
        for child, (group, extension) in items[offset:offset + chunk_size]:
            parent = group["gap16_id"]
            mask = extension["cocycle"]
            basis_prefix = "parent14" if parent == 14 else f"coverageP{parent}"
            coefficients = f"(coeffMask {group['h2_dimension']} {extension['h2_mask']})"
            lines.extend([
                f"def cocycle{child} := CertifiedTableGroup.encodedCocycle parent{parent}Table {mask}",
                f"theorem cocycle{child}_consistent : IsCentralCocycle cocycle{child} := by",
                f"  have hdecode : cocycle{child} = Order16Table.decodeTwo parent{parent}Table",
                f"      (synthesizeTwo {basis_prefix}HBasis {coefficients}) := by decide +kernel",
                "  rw [hdecode]",
                f"  exact Order16Table.isCentralCocycle_decodeTwo_synthesize parent{parent}Table",
                f"    {basis_prefix}HBasis orbitP{parent}_hbasis_cocycle _",
                f"abbrev generatedGroup{child} := CocycleGroup cocycle{child} cocycle{child}_consistent",
                f"theorem card_generatedGroup{child} : Nat.card generatedGroup{child} = 32 := by",
                "  rw [CocycleGroup.card_eq]",
                "  norm_num [Nat.card_eq_fintype_card, ZMod.card]",
                "",
            ])
        lines.extend(["end Smallgroups.UsefulTheorems.Order32Certificate", ""])
        (output_dir / f"{part_name}.lean").write_text("\n".join(lines), encoding="utf-8")

    umbrella = [header.rstrip()]
    umbrella.extend(
        f"import Smallgroups.UsefulTheorems.Order32Certificate.{name}" for name in part_names
    )
    umbrella.extend([
        "",
        "/-! Generated 51 GAP-indexed central-extension representatives of order 32. -/",
        "",
    ])
    (output_dir / "Reps.lean").write_text("\n".join(umbrella), encoding="utf-8")
    family = [
        header.rstrip(),
        "import Smallgroups.UsefulTheorems.Order32Certificate.Reps",
        "import Mathlib.Tactic",
        "",
        "/-! Generated fallback-free `Fin 51` family; do not edit. -/",
        "",
        "namespace Smallgroups.UsefulTheorems.Order32Certificate",
        "",
    ]
    sizes = [8, 8, 8, 8, 8, 8, 3]
    start = 1
    for part, size in enumerate(sizes, start=1):
        tag = f"{part:02d}"
        family.append(f"abbrev generatedFamilyPart{tag} : Fin {size} → Type")
        for i in range(size):
            family.append(f"  | {i} => generatedGroup{start + i}")
        family.append("")
        family.append(f"instance instGroupGeneratedFamilyPart{tag} :")
        family.append(f"    ∀ i, Group (generatedFamilyPart{tag} i)")
        for i in range(size):
            family.append(
                f"  | {i} => inferInstanceAs (Group generatedGroup{start + i})"
            )
        family.append("")
        family.append(f"theorem card_generatedFamilyPart{tag} :")
        family.append(f"    ∀ i, Nat.card (generatedFamilyPart{tag} i) = 32")
        for i in range(size):
            family.append(f"  | {i} => card_generatedGroup{start + i}")
        family.append("")
        start += size
    family.extend([
        "/-- The 51 generated central extensions, indexed by GAP id minus one. -/",
        "def generatedFamily (i : Fin 51) : Type :=",
        "  if h1 : i.1 < 8 then generatedFamilyPart01 ⟨i.1, h1⟩",
        "  else if h2 : i.1 < 16 then generatedFamilyPart02 ⟨i.1 - 8, by omega⟩",
        "  else if h3 : i.1 < 24 then generatedFamilyPart03 ⟨i.1 - 16, by omega⟩",
        "  else if h4 : i.1 < 32 then generatedFamilyPart04 ⟨i.1 - 24, by omega⟩",
        "  else if h5 : i.1 < 40 then generatedFamilyPart05 ⟨i.1 - 32, by omega⟩",
        "  else if h6 : i.1 < 48 then generatedFamilyPart06 ⟨i.1 - 40, by omega⟩",
        "  else generatedFamilyPart07 ⟨i.1 - 48, by omega⟩",
        "",
        "instance instGroupGeneratedFamily (i : Fin 51) : Group (generatedFamily i) := by",
        "  unfold generatedFamily",
        "  split",
        "  · infer_instance",
        "  · split",
        "    · infer_instance",
        "    · split",
        "      · infer_instance",
        "      · split",
        "        · infer_instance",
        "        · split",
        "          · infer_instance",
        "          · split <;> infer_instance",
        "",
        "theorem card_generatedFamily (i : Fin 51) : Nat.card (generatedFamily i) = 32 := by",
        "  unfold generatedFamily",
        "  split",
        "  · exact card_generatedFamilyPart01 _",
        "  · split",
        "    · exact card_generatedFamilyPart02 _",
        "    · split",
        "      · exact card_generatedFamilyPart03 _",
        "      · split",
        "        · exact card_generatedFamilyPart04 _",
        "        · split",
        "          · exact card_generatedFamilyPart05 _",
        "          · split",
        "            · exact card_generatedFamilyPart06 _",
        "            · exact card_generatedFamilyPart07 _",
        "",
        "end Smallgroups.UsefulTheorems.Order32Certificate",
        "",
    ])
    (output_dir / "Family.lean").write_text("\n".join(family), encoding="utf-8")

    alignment_names = []
    for part_index, offset in enumerate(range(0, len(items)), start=1):
        part_name = f"AlignmentPart{part_index:02d}"
        alignment_names.append(part_name)
        child, (_, extension) = items[offset]
        reps_part = (child - 1) // chunk_size + 1
        gap_part = (child - 1) // 16 + 1
        lines = [
            header.rstrip(),
            f"import Smallgroups.UsefulTheorems.Order32Certificate.RepsPart{reps_part:02d}",
            f"import Smallgroups.GAP.Polycyclic.Imported.Order32Part{gap_part:02d}",
        ]
        lines.append("import Smallgroups.GAP.Polycyclic.PresentationHom")
        lines.extend([
            "",
            "set_option maxRecDepth 100000",
            "set_option linter.style.longLine false",
            "",
            "/-! Generated explicit alignment maps to GAP pc presentations; do not edit. -/",
            "",
            "namespace Smallgroups.UsefulTheorems.Order32Certificate",
            "",
            "open Smallgroups.GAP",
            "",
        ])
        for child, (_, extension) in items[offset:offset + 1]:
            exponents = "![" + ", ".join(
                "[" + ", ".join(map(str, row)) + "]"
                for row in extension["pc_exponents"]
            ) + "]"
            lines.extend([
                f"def gapExponents{child} : Fin 32 → List ℕ := {exponents}",
                f"def generatedToGap{child} (x : generatedGroup{child}) :",
                f"    PCGroup smallGroup_32_{child} :=",
                f"  evalVec (gapExponents{child} (certifiedExtensionIndex x))",
                f"    (pcGens smallGroup_32_{child}.layers)",
                "",
            ])
            lines.extend(relation_alignment_lines(
                f"generatedGroup{child}",
                f"generatedRelation{child}",
                f"generatedToGap{child}",
                f"generatedGapEquiv{child}",
                child,
                extension["pc_exponents"],
                f"by rw [card_smallGroup_32_{child}, card_generatedGroup{child}]",
            ))
            lines.append("")
        lines.extend(["end Smallgroups.UsefulTheorems.Order32Certificate", ""])
        (output_dir / f"{part_name}.lean").write_text("\n".join(lines), encoding="utf-8")

    alignment = [header.rstrip()]
    alignment.extend(
        f"import Smallgroups.UsefulTheorems.Order32Certificate.{name}"
        for name in alignment_names
    )
    alignment.extend([
        "import Smallgroups.UsefulTheorems.Order32Certificate.Family",
        "import Smallgroups.GAP.Order32",
        "",
        "/-! Generated GAP alignment for all 51 representatives. -/",
        "",
        "namespace Smallgroups.UsefulTheorems.Order32Certificate",
        "",
        "open Smallgroups.GAP",
        "",
    ])
    for part in range(7):
        start = part * 8 + 1
        stop = min(start + 8, 52)
        size = stop - start
        part_name = f"{part + 1:02d}"
        alignment.extend([
            f"noncomputable def generatedFamilyGapEquivPart{part_name} : ∀ i : Fin {size},",
            f"    generatedFamilyPart{part_name} i ≃* PCGroup (smallPres32Part{part_name} i)",
        ])
        for offset, group_id in enumerate(range(start, stop)):
            alignment.append(f"  | {offset} => generatedGapEquiv{group_id}")
        alignment.append("")
    alignment.extend([
        "theorem generatedFamilyGapEquiv_nonempty (i : Fin 51) :",
        "    Nonempty (generatedFamily i ≃* smallGroup32 i) := by",
        "  fin_cases i",
    ])
    for group_id in range(1, 52):
        alignment.append(f"  · exact ⟨generatedGapEquiv{group_id}⟩")
    alignment.extend([
        "",
        "noncomputable def generatedFamilyGapEquiv (i : Fin 51) :",
        "    generatedFamily i ≃* smallGroup32 i :=",
        "  (generatedFamilyGapEquiv_nonempty i).some",
    ])
    alignment.extend([
        "",
        "end Smallgroups.UsefulTheorems.Order32Certificate",
        "",
    ])
    (output_dir / "Alignment.lean").write_text("\n".join(alignment), encoding="utf-8")
    # Some legacy emitters above are retained temporarily as readable migration code;
    # ensure their outputs are absent from the final generated source tree.
    for pattern in obsolete_patterns:
        for path in output_dir.glob(pattern):
            path.unlink()
    for name in obsolete_names:
        path = output_dir / name
        if path.exists():
            path.unlink()
    print(f"wrote Lean certificate modules under {output_dir}")


def check_lean_certificates(groups, output_dir: Path):
    """Regenerate into a temporary directory and compare every emitted Lean module."""
    with tempfile.TemporaryDirectory(prefix="smallgroups-order32-") as temporary:
        generated_dir = Path(temporary)
        emit_lean_certificates(groups, generated_dir)
        generated = {path.name: path for path in generated_dir.glob("*.lean")}
        missing = sorted(name for name in generated if not (output_dir / name).is_file())
        changed = sorted(
            name for name, path in generated.items()
            if (output_dir / name).is_file()
            and path.read_text(encoding="utf-8")
                != (output_dir / name).read_text(encoding="utf-8")
        )
        retired = sorted({
            path.name
            for pattern in (*OBSOLETE_CERTIFICATE_PATTERNS, *OBSOLETE_CERTIFICATE_NAMES)
            for path in output_dir.glob(pattern)
        })
        if missing or changed or retired:
            raise RuntimeError(
                "generated Lean certificate mismatch: "
                f"missing={missing}, changed={changed}, retired={retired}"
            )
        print(f"checked {len(generated)} generated Lean certificate modules")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--gap-bash", type=Path, default=None)
    parser.add_argument("--gap-exe", default=None)
    parser.add_argument("--summary", action="store_true", help="compute and print a summary only")
    parser.add_argument(
        "--output", type=Path,
        default=REPO / "Certificates" / "Order32" / "central_extensions.json",
    )
    parser.add_argument("--emit-lean", action="store_true")
    parser.add_argument(
        "--check-lean", action="store_true",
        help="regenerate Lean modules in a temporary directory and compare them",
    )
    parser.add_argument(
        "--from-json", action="store_true",
        help="reuse the existing JSON certificate and only regenerate Lean modules",
    )
    args = parser.parse_args()
    if args.from_json:
        payload = json.loads(args.output.read_text(encoding="utf-8"))
        groups = payload["parents"]
        for group in groups:
            refresh_shortest_orbit_words(group)
        lean_output_dir = REPO / "Smallgroups" / "UsefulTheorems" / "Order32Certificate"
        if args.check_lean:
            check_lean_certificates(groups, lean_output_dir)
        elif args.emit_lean:
            emit_lean_certificates(
                groups, lean_output_dir
            )
        return
    gap_bash = args.gap_bash or default_gap_bash()
    gap_exe = args.gap_exe or default_gap_exe(gap_bash)

    groups = [cocycle_data(g) for g in gap_order16_data(gap_bash, gap_exe)]
    identify_extensions(groups, gap_bash, gap_exe)
    covered = sorted({e["gap32_id"] for g in groups for e in g["extensions"]})
    for g in groups:
        ids = sorted({e["gap32_id"] for e in g["extensions"]})
        print(
            f"SmallGroup(16,{g['gap16_id']}): "
            f"dim Z2/B2/H2={g['z2_dimension']}/{g['b2_dimension']}/{g['h2_dimension']}, "
            f"orbits={len(g['extensions'])}, GAP32={ids}"
        )
    print(f"union: {len(covered)} GAP ids: {covered}")

    if not args.summary:
        payload = {"format": 1, "coefficient": "ZMod 2", "parents": groups}
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"wrote {args.output}")
        lean_output_dir = REPO / "Smallgroups" / "UsefulTheorems" / "Order32Certificate"
        if args.check_lean:
            check_lean_certificates(groups, lean_output_dir)
        elif args.emit_lean:
            emit_lean_certificates(
                groups, lean_output_dir
            )


if __name__ == "__main__":
    main()
