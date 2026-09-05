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

## Relation-based GAP alignment

The 51 standard representatives and 14 order-16 parent maps no longer ask
`decide +kernel` to check all pairs in a 16- or 32-element multiplication table.  The
generic constructor in
`GAP/Polycyclic/PresentationHom.lean` proves that a map out of one `CycExt` layer is a
homomorphism when the image of its new generator satisfies that layer's power and
conjugation relations.  Generated alignments apply this theorem recursively through
the pc tower, then check one explicit right inverse and use equality of finite
cardinalities to obtain a `MulEquiv`.

The other 47 coverage representatives now use an explicit indexed equivalence to the
already verified standard representative with the same GAP id, then compose with its
GAP equivalence.  Thus the certificate has 65 direct pc relation maps rather than 112,
and none of its former 112 `mulEquivOfDecide` calls remain.  All relation, multiplication,
and inverse obligations are ordinary kernel-checked proof terms.  A CI audit rejects
`bv_decide`, `native_decide`, `sorry`, `admit`, `axiom`, and `unsafe` in the Order-32
certificates and the local Polycyclic and PGroupGeneration proof infrastructure.

Generated alignment imports are also split by the exact representative and GAP data
chunks they use.  Standard alignments, parent-table alignments, and coverage alignments
no longer form artificial serial import chains; the aggregate modules remain the only
place that imports all parts.

The relation theorem extends conjugation from a generating list to the entire
inner group. Each order-32 alignment therefore checks five power relations and ten
generator conjugation relations, then a 32-entry right inverse. All 51 standard maps
and all 14 parent maps passed local compilation. With precise imports and `lean -j1`,
the standard modules took 16.573--24.690 seconds each (median 18.186 seconds), with
1.28--1.32 GiB peak working set. `AlignmentPart01` took 19.532 seconds; the earlier
local baseline was 102.705 seconds. These measurements combine the source and import
improvements and use the stated local invocation; CI timings are reported separately.

The CycExt infrastructure imports `Mathlib.Tactic.Group` and `SplitIfs` explicitly,
and the certified-table infrastructure imports `FinCases` and `NormNum`. This avoids
loading the full `Mathlib.Tactic` umbrella into every certificate. Explicit PUnit and
ZMod field imports preserve the instances previously supplied indirectly.

## Shared cocycle basis proofs

The fourteen `CocycleBasisParentNN` modules check the 55 H² basis vectors once.  Coverage
modules and standard representatives import the same proofs.  Each of the 51 standard
representatives checks equality of its encoded cocycle with the corresponding linear
combination on pairs of elements, then applies
`Order16Table.isCentralCocycle_decodeTwo_synthesize`.  The representative no longer
repeats the cocycle identity on all triples.  Its group law still uses the original
packed cocycle, so downstream computations do not repeatedly evaluate the linear sum.

## Interpreting CI measurements

The successful `969dc66` [CI baseline](https://github.com/lixiang90/smallgroups/actions/runs/33864362685)
spent 5400.916 seconds on certificates, 93 seconds on the final project build, and 2171
seconds on documentation.  It was a mixed-cache run: all 51 standard alignments, all 14
parent alignments, and the representative modules were replayed.  The 47 direct coverage
maps were actually rebuilt and took 2114.875 seconds in aggregate.  Parent 14's sixteen
forest checks took 353.320 seconds.

The old workflow saved its Lean cache before the custom certificate build.  The workflow
now restores a separately versioned cache, checks generated-source consistency, and saves
the cache only after both certificate and project builds pass, before changing the
documentation target.  The first run in the new cache namespace must rebuild more
modules.  Compare individual rebuilt modules or runs with matching cache conditions;
neither total time nor a cached replay is evidence of a proof-compilation speedup.

## Parent 14 orbit forest

Parent 14 is the elementary abelian quotient `(C₂)^4`.  Its `H²` coordinate space has
dimension 10, hence 1024 vectors, four checked orbit generators, and seven orbits.  The
old certificate expanded a shortest word separately for every vector: 64 generated
`CoverageOrbitParent14PathPartNN` files, 1024 separately constructed extension
isomorphisms, and a large `fin_cases` dispatcher in `PathIdentity`.

The first stage emitted a shortest-path forest instead.  For every vector it records a
parent, final generator, and rank; roots are the seven representative masks
`[0, 1, 2, 19, 20, 40, 184]`.  Sixteen independent chunks check 64 local edges each.
`OrbitReduction.lean` proves once, by well-founded recursion on rank, that following the
parent pointers reaches the requested vector.  `orbitP14NormalizeEquiv` keeps its old
type and name, but is now assembled by this generic theorem rather than by 1024 generated
proof terms.

The second stage keeps the same seven Parent 14 cocycles and composes their GAP maps
through the standard representatives. The forest described above is now retired.  The earlier 1024-entry normalization data/core pair and
seven pilot alignment modules remain unnecessary.

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
`decide +kernel` occurrences.  The first-stage certificate directory contained 391 Lean files.
A clean parallel GitHub build was the full-suite baseline: it was
terminated with exit 143 before producing a wall-clock result.  The current topological
inventory is printed reproducibly by:

```text
python Scripts/build_order32_serial.py --dry-run
```

The scheduler isolates every module containing `decide +kernel`; modules without kernel
decisions use topological batches of at most four targets.  Its printed inventory includes
the shared cocycle basis and additional structural modules.  This conservative policy
was adopted after a CI runner terminated the initial batch of `Tables` and three
`RepsPart` modules, which together contained 95 kernel decisions.  Passing
`--batch-size 1` restores one-target-per-process behavior.  The CI command below is the
authoritative full-suite post-change measurement and retains the successful serial
build's memory bound.

## Evaluator choice

All finite certificate checks use `decide +kernel`.  Python and GAP supply only data
and witnesses; the Lean kernel verifies every mathematical obligation.  Native or
bitvector decision procedures that expand the trusted computing base are excluded.
The former forest used sixteen independent 64-edge checks to bound memory; the second
stage removes them entirely through ordinary mathematical theorems.

## Structural quadratic classification for Parent 14

`QuadraticDimensionFour.lean` proves that every quadratic space of dimension four over
`F₂` is isometric to one of seven forms: zero, one square, `H`, `A`, `H` plus one
square, `H ⊥ H`, or `H ⊥ A`. The proof splits off a nondegenerate plane, classifies the
two-dimensional remainder, absorbs square coefficients into a radical vector when its
square is nonzero, and uses the explicit identity `A ⊥ A ≃ H ⊥ H`. With zero polarization,
the quadratic map is a linear functional and is classified using its kernel.

`QuadraticNormalForms4Distinct.lean` separates these forms using their zero counts
`[16, 8, 12, 4, 8, 10, 6]` together with whether polarization vanishes. These are proved
isometry invariants. This gives the required separation without a separate abstract
Arf-invariant quotient construction. `QuadraticInvariants.lean` additionally proves
polar-kernel transport and dimension invariance and defines the linear restriction of
the quadratic map to that kernel.

`Parent14QuadraticRepresentatives.lean` supplies seven explicit invertible coordinate
matrices to the existing masks `[0, 1, 2, 19, 20, 40, 184]`. The kernel checks the small
coordinate identities and transfers pairwise inequivalence to the existing representatives.
`QuadraticCocycleSplitting.lean` proves that equal square maps differ by a coboundary,
using an ordinary linear section of an abelian exponent-two extension, and consequently
that isometric square maps give isomorphic cocycle groups.

`Parent14QuadraticClassification.lean` applies these results directly to any normalized
cocycle on Parent 14. `orbitP14_cocycle_orbit_complete` retains its public statement but
now invokes this structural proof. The 1024-vertex forest, its sixteen checking modules,
the forest aggregate, and the unnecessary Parent 14 cohomology-decomposition and packed
identity modules are removed (22 retired source modules in total). The generator emits
only the seven selected cocycles, their compositional GAP maps, and the structural
completeness wrapper for this parent, and its reproducibility check rejects retired files.

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
finite checks together. Large finite checks remain isolated even after the structural
replacement and the reduction in alignment cost.
