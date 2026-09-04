# Order-32 classification certificates

These files are generated data, not trusted proofs. Lean decodes them through the
modules in `Smallgroups/UsefulTheorems/Order32Certificate` and checks every group table,
cocycle equation, GF(2) reduction, automorphism action, orbit path, PC-generator map,
and distinctness profile in the kernel.

The recorded generator environment is:

- Lean 4.32.2 and mathlib v4.32.2;
- GAP 4.16.1;
- GAP package `smallgrp` 1.7.0;
- GAP package `anupq` 3.3.3 (recorded for reproducibility; the present certificate
  generator uses SmallGroups, PC groups, and automorphism groups, not an unverified
  ANUPQ classification assertion).

Run `python Scripts/query_gap_versions.py` to report these GAP-side versions in the
configured runtime.

Regenerate the PC presentations and central-extension data from GAP with:

```text
python Scripts/translate_pc.py --chunk-size 16 32
python Scripts/generate_order32_cohomology.py --emit-lean
python Scripts/analyze_order32_fingerprints.py --emit-lean
```

To reproduce only the Lean source modules from the checked-in JSON data:

```text
python Scripts/generate_order32_cohomology.py --from-json --emit-lean
```

To verify reproducibility without modifying the worktree, regenerate all emitted Lean
modules in a temporary directory and compare their newline-normalized text:

```text
python Scripts/generate_order32_cohomology.py --from-json --check-lean
```

The local-profile generator is intentionally rerun against GAP; its resulting values
are only hints, since every one of the 51 profiles is recomputed independently in Lean.

`generate_order32_cohomology.py` rejects missing/reordered order-16 parents, malformed
multiplication tables or automorphisms, malformed PC exponent maps, and any final GAP-ID
coverage other than exactly `1..51`. `translate_pc.py` likewise rejects missing,
duplicate, or reordered GAP IDs, so there is no fallback group.

The certificate hashes for this generated snapshot are:

```text
central_extensions.json  AFC69BB26DA8E737CFF2F2B43FC70C6482D5CF09B7305E764726CC1F97570F86
local_profiles.json      37A2D58A9A03BC64A443C8EFA6E878434912C8EA7F762E5916A410125D0709A9
```

## Parent 14 orbit forest

Parent 14 is the elementary abelian quotient `(C₂)^4`.  Its `H²` coordinate space has
dimension 10, hence 1024 vectors, four checked orbit generators, and seven orbits.  The
old certificate expanded a shortest word separately for every vector: 64 generated
`CoverageOrbitParent14PathPartNN` files, 1024 separately constructed extension
isomorphisms, and a large `fin_cases` dispatcher in `PathIdentity`.

The generator now emits a shortest-path forest instead.  For every vector it records a
parent, final generator, and rank; roots are the seven representative masks
`[0, 1, 2, 19, 20, 40, 184]`.  Sixteen independent chunks check 64 local edges each.
`OrbitReduction.lean` proves once, by well-founded recursion on rank, that following the
parent pointers reaches the requested vector.  `orbitP14NormalizeEquiv` keeps its old
type and name, but is now assembled by this generic theorem rather than by 1024 generated
proof terms.

The GAP maps for the seven Parent 14 representatives now target the forest-selected
cocycles directly.  This removes the earlier 1024-entry normalization data/core pair,
seven pilot alignment modules, and seven extra cocycle-equality kernel checks.

The following Windows measurements used Lean/mathlib 4.32.2 on this checkout.  Commands
were run with the toolchain's `lake.exe`; wall times include import/cache loading.

| Check | Before / experiment | Result |
|---|---:|---|
| `Tables.lean` | 86.28 s | reference baseline |
| `CoverageLinearParent01BatchIdentity` | 95.69 s | reference baseline |
| `CoverageOrbitParent14Core` | 231.65 s | reference baseline |
| one old Parent 14 path part | 19.58 s | 64 files, roughly 17–21 min in aggregate |
| one giant forest `decide +kernel` | >180 s, 5.36 GiB | interrupted; rejected design |
| 16 checks in one Lean process | >5.25 GiB | interrupted; rejected design |
| 16 independent forest chunks | 16–43 s each, 474 s total | all passed serially |
| new `PathIdentity` aggregate | 12 s | passed |
| representative forest chunk peak | about 1.8 GiB | one Lean process |
| all 400 certificate modules, topologically serialized | about 3 h 58 min | pre-batching baseline on a loaded Windows workstation |
| subsequent full `lake build` | 296.42 s (4.94 min) | passed with the certificate cache populated |

The former generated tree contained 446 Lean files and 32,883 lines, including 1,802
`decide +kernel` occurrences.  The current certificate directory contains 391 Lean files.
A clean parallel GitHub build was the full-suite baseline: it was
terminated with exit 143 before producing a wall-clock result.  The current topological
inventory is printed reproducibly by:

```text
python Scripts/build_order32_serial.py --dry-run
```

With the default batch size it schedules 391 modules in 205 Lake invocations: the 16
measured high-memory forest chunks and 112 direct PC-map modules remain isolated, while
the other modules use 77 topological batches of at most four targets.  Passing
`--batch-size 1` restores one-target-per-process behavior.  The CI command below is
the authoritative full-suite
post-change measurement and avoids an unreproducible OOM result.

## Evaluator choice

The forest keeps `decide +kernel`, but only for 64-edge local certificates.  This choice
was measured rather than applied globally:

- a single packed native check (`native_decide`) had not completed after 200 seconds;
- `bv_decide` rejected the edge predicate because it is not wholly in its supported
  `BitVec` fragment;
- a giant kernel decision accumulated more than 5 GiB;
- independent 64-edge kernel checks completed with bounded per-process memory.

The large `Nat` masks therefore remain at the trusted decoding boundary for now.  A
future BitVec conversion should first isolate a pure fixed-width boolean checker and
prove a reflection theorem back to `OrbitForestEdge`; merely changing storage types does
not make the current higher-order cocycle predicate suitable for `bv_decide`.

## Quadratic-form bridge and remaining work

`PGroupGeneration/QuadraticCocycle.lean` constructs the square quadratic map of a central
`C₂` cocycle and proves that its polar form is the commutator pairing, that normalized
coboundaries do not change it, and that it commutes with linear pullback.
`Order32Certificate/Parent14Quadratic.lean` gives an explicit checked equivalence between
the Parent 14 table and `F₂⁴`, transports its cocycles, and proves that representative 0
is the zero quadratic normal form.  Existing seven-orbit completeness is re-exported next
to this structural interface, so downstream classification and GAP numbering are
unchanged.

Completing the replacement of the remaining orbit computation requires these lemmas:

1. define the rank of the polar linear map and prove invariance under `GL(4,2)`;
2. define its radical and the restriction of the quadratic map to that radical;
3. define the Arf invariant on the nondegenerate quotient and prove coordinate invariance;
4. calculate `(polar rank, radical restriction, Arf)` for all seven representatives and
   prove that the tuples separate them;
5. formalize the characteristic-two Witt reduction showing every four-dimensional
   quadratic map is equivalent to one of those seven forms.

Until those structural lemmas land, the checked forest supplies completeness while the
quadratic invariants can be developed and tested independently.

## Low-memory build

Lake 5 schedules independent jobs concurrently and has no job-count option.  Do not encode
resource scheduling as cross-module mathematical imports.  Build the generated modules
with bounded topological batches, then run the ordinary project build:

```text
python Scripts/build_order32_serial.py --timings-json .lake/order32-build-timings.json
lake build
```

The JSON report records each batch, its modules, status, and elapsed wall time; CI uploads
it even when a batch fails.  On Windows, the script also avoids launching the measured
approximately 1.8 GiB forest checks or the multi-gigabyte PC-map checks together.
