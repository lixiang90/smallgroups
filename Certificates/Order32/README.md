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

On Windows, build the generated leaf modules in small batches or one at a time. Several
finite PC checks can each use about 2 GiB during elaboration, so asking Lake to rebuild
many independent alignment parts simultaneously can exceed physical memory.
