# smallgroups

Formalizing the classification of small finite groups in **Lean 4 + Mathlib**.

## Goal

For each small order `n`, a *full classification* of groups of order `n` consists of three
theorems:

1. **Exhaustiveness** — exhibit all possible isomorphism classes and prove every group of
   order `n` is one of them.
2. **Distinctness** — prove the listed classes are pairwise non-isomorphic.
3. **Counting** — count the isomorphism classes.

## Done so far:

| Category | Orders | # | Representatives | Via |
|----------|--------|---|-----------------|-----|
| trivial | 1 | 1 | `ℤ/1` | — |
| prime | 2,3,5,7,11,13,17,19,23,29,31,37,41,<br>43,47,53,59,61,67,71,73,79,83,89,97 | 1 | `ℤ/N` | `PrimeOrderCyclic` |
| `p²` | 4,9,25,49 | 2 | `ℤ/N`, `ℤ/p × ℤ/p` | `PrimeSqClassification` |
| `p·q` (`q ∤ p−1`) | 15,33,35,51,65,69,77,85,87,91,95 | 1 | `ℤ/N` | `PrimePairCyclic` |
| `2p` | 6,10,14,22,26,34,38,46,<br>58,62,74,82,86,94 | 2 | `ℤ/2p`, `D_p` | `PrimePairDihedral` |
| `p·q` (`q ∣ p−1`) | 21,39,55,57,93 | 2 | `ℤ/pq`, `ℤ/p ⋊ ℤ/q` | `PrimePairNonabelian` |
| `p³` | 8,27 | 5 | 5 types | `P3Group` |
| `2p²` | 18,50,98 | 5 | 5 types | `Order2PSq` |
| `p²q` (`p∤q−1`, `q∤p²−1`) | 45,99 | 2 | `ℤ/p²q`, `ℤ/p × ℤ/pq` | `PrimeSqPrimeAbelian` |
| `p²q` (`q ∣ p−1`) | 75 | 3 | `ℤ/p²q`, `ℤ/p × ℤ/pq`, `(ℤ/p)² ⋊ ℤ/q` | `PrimeSqPrimeNonabelian` |
| `4p` (`p ≥ 5`) | 20,28,44,52,68,76,92 | 4 or 5 | 5 types (mod 1) / 4 types (mod 3) | `Order4P` |
| `4·3` | 12 | 5 | `ℤ/12`, `ℤ/2×ℤ/6`, `Dic₃`, `ℤ/2×S₃`, `A₄` | `Order4P_12` |
| `2pq` (`2<p<q`, `p∤q−1`) | 30,66,70 | 4 | `ℤ/2pq`, `D_pq`, `ℤ/q×D_p`, `ℤ/p×D_q` | `Order2PQ` |
| `2pq` (`2<p<q`, `p∣q−1`) | 42,78 | 6 | + `(ℤ/q⋊ℤ/p)×ℤ/2`, `ℤ/q⋊ℤ/2p` | `Order2PQ` |
| `4·3²` | 36 | 14 | normal Sylow-`3` branch plus `C₃×A₄`, `A₄×_{C₃}C₉` | `Order36` |
| `2·3³` | 54 | 15 | Schur--Zassenhaus representatives over the order-27 kernels | `Order54` |
| `7·3²` | 63 | 4 | `ℤ/63`, `ℤ/3×ℤ/21`, `(ℤ/7⋊ℤ/3)×ℤ/3`, `ℤ/7⋊ℤ/9` | `Order63` |
| `8·5` | 40 | 14 | `ℤ/5 ⋊ H` (`H` of order 8) — 14 actions | `Order40` |
| `8·7` | 56 | 13 | two Sylow cases: `ℤ/7 ⋊ H` and one `(ℤ/2)³ ⋊ ℤ/7` case | `Order56` |
| `8·11` | 88 | 12 | `ℤ/11 ⋊ H` (`H` of order 8) — 12 actions | `Order88` |
| `4·5²` | 100 | 16 | `P ⋊ H` with &#124;P&#124; = 25, &#124;H&#124; = 4 — 16 actions | `Order100` |
| `2⁴` (Wild) | 16 | 14 | 5 abelian types + 9 `C₈`/`K₈`-extension types | `Order16_Wild` |
| `3·8` | 24 | 15 | twelve `C₃ ⋊ H` cases, two normal Sylow-`2` cases, and `S₄` | `Order24` |
| `12·7` | 84 | 15 | `C₇ ⋊ H` with &#124;H&#124; = 12 — 15 actions over the 5 order-12 types | `Order84` |
| `5·12` | 60 | 13 | 12 solvable `ℤ/5 ⋊[φ] K` (`K` of order 12) + `A₅` | `Order60.Classification` |
| `2·3²·5` | 90 | 10 | `N ⋊ C₂` with &#124;N&#124; = 45 — 10 involutions over the 2 order-45 types | `Order90` |
| `2⁴·5` | 80 | 52 | 51 `C₅ ⋊[χ] K` (normal Sylow-5, `K` one of 14 order-16 types) + `(C₂)⁴ ⋊ C₅` | `Order80` |
| `3⁴` | 81 | 15 | 5 abelian types + 10 non-abelian types over a `ℤ/9×ℤ/3` or `(ℤ/3)³` kernel | `Order81` |
| `2³·3²` | 72 | 50 | 42 normal-Sylow-`3` semidirects `K ⋊ H`, 14 normal-Sylow-`2` (10 direct products shared), 4 residual (`S₃×A₄`, `C₃×S₄`, `C₃⋊S₄`, `C₃.S₄`) † | `Order72` |

† Order 72: exhaustiveness currently rests on one axiom,
`order72_residual_kernel_cases_to_repCases` (the conversion of the residual branch's
kernel/image analysis into the four explicit residual groups); distinctness is fully
machine-checked.

## Layout

* `Smallgroups/UsefulTheorems/` — reusable tools for classification.
  * `PrimeOrderCyclic.lean` — a finite group of prime order is cyclic
    (`Smallgroups.isCyclic_of_card_eq_prime`).
    
  * `PrimeOrderClassification.lean` — the shared engine for single-class (cyclic) orders:
    `CyclicRep n = ℤ/n`, `cyclicRep_classification`, `prime_classification`, `prime_unique`,
    and the `singleReps` distinctness scaffolding.
    
  * `PrimeSqClassification.lean` — the engine for orders `p²`: `prime_sq_mul_comm` (such groups
    are abelian), `prime_sq_classification` (every group of order `p²` is `ℤ/p²` or
    `ElemAbelianRep p = ℤ/p × ℤ/p`, proved via the `ℤ/p`-vector space structure of the non-cyclic
    case), and `prime_sq_distinct` (the two are non-isomorphic).
    
  * `PrimePairCyclic.lean` — the engine for orders `p * q` (`p > q` distinct primes) in the
    cyclic case: `isCyclic_of_card_eq_prime_mul` shows that when `q ∤ p - 1`, both Sylow subgroups
    are normal (Sylow counting), so the group is nilpotent and, being a squarefree-order `Z`-group,
    cyclic.
    
  * `PrimePairDihedral.lean` — the engine for orders `2p` (`p` an odd prime), the smallest
    `q ∣ p - 1` case: `classification_card_two_mul_prime` shows every group of order `2p` is the
    cyclic group `ℤ/2p` or the dihedral group `DihedralGroup p` (an index-2 cyclic subgroup forces
    conjugation by an involution to invert it, giving either the abelian/cyclic or the dihedral
    relation), and `cyclicRep_not_mulEquiv_dihedral` separates the two classes.
    
  * `PrimePairNonabelian.lean` — the non-abelian case for general `q ∣ p - 1`:
    `NonabRep c hc = ℤ/p ⋊ ℤ/q` (semidirect product for the action by a unit `c` of order `q`), with
    `card_nonabRep` (order `p·q`), `not_isCyclic_nonabRep`, `cyclicRep_not_mulEquiv_nonabRep`, and
    `exists_unit_orderOf_eq` (an order-`q` unit exists). **The full classification is complete:**
    `nonempty_mulEquiv_nonabRep` (a group with the right generators is `≅ NonabRep c`, via
    `SemidirectProduct.lift` + cardinality), `exists_generators_of_card_eq_prime_mul` (the Sylow
    setup), `unit_mem_zpowers_of_pow_eq` (relabelling), and `classification_card_eq_prime_mul`:
    every group of order `p·q` is cyclic or `≅ NonabRep c₀`.
    
  * `SchurZassenhaus.lean` — the **Schur–Zassenhaus theorem** packaged for classification. Mathlib
    proves the theorem itself (`Subgroup.exists_right_complement'_of_coprime`); this file combines it
    with `SemidirectProduct.mulEquivSubgroup` into the semidirect-product form the project uses:
    `schurZassenhaus_semidirectProduct` (a finite group with a coprime-index normal subgroup `N` is
    `G ≃* N ⋊[φ] K`) and `schurZassenhaus_of_card` (the same via a coprime factorisation
    `|G| = m * n` with `|N| = m`). This is the general form of the ad-hoc semidirect-product splitting
    used for orders `pq` and `p³`.

  * `SemidirectProductClassify.lean` — tools for classifying the semidirect products `N ⋊[φ] H` by
    their action `φ : H →* MulAut N` (the natural follow-up to Schur–Zassenhaus). The action is
    recovered from the group by `φ h n = (inr h * inl n * (inr h)⁻¹).left` (`conjAction_eq`), so the
    parametrisation is **faithful**: an isomorphism fixing `inl`/`inr` forces `φ = ψ`
    (`semidirectProduct_action_inj`). The constructive iso direction is `semidirectProductCongr` (from
    `θ : N ≃* N'`, `σ : H ≃* H'` intertwining the actions, build `N ⋊[φ] H ≃* N' ⋊[φ'] H'`), with the
    orbit-move corollaries `semidirectProductCongrAut` (precompose `φ` with `Aut H`),
    `semidirectProductCongrConj` (conjugate `φ` by `Aut N`), and `semidirectProductCongr_eq`. So two
    actions in the same `Aut N × Aut H`-orbit give isomorphic groups.

  * `PrimeSqPrime.lean` — the structural reduction for orders `p² q` with `p ∤ q − 1` (which already
    forces `p` odd). Sylow counting gives `n_p ∈ {1, q}` with `n_p = q ⇒ p ∣ q − 1`, so the Sylow
    `p`-subgroup is unique and normal (`card_sylow_p_eq_one_of_card_psq`,
    `sylow_p_normal_of_card_psq`); it has order `p²` (`card_sylow_p_subgroup_of_card_psq`, hence
    abelian). Schur–Zassenhaus then splits `G ≃* P ⋊[φ] K` with `P` normal of order `p²` and `K` of
    order `q` (`psq_semidirectProduct`), reducing the classification to the action `φ : K → Aut P`
    (which the further count — depending on `q ∣ p ± 1` and the structure of `P` — leaves to the
    per-order files).

  * `Order4Prime.lean` — the first reduction for the `4p` family with `p > 4`. Sylow counting shows
    that the Sylow `p`-subgroup is unique and normal
    (`card_sylow_p_eq_one_of_card_four_mul_prime`, `sylow_p_normal_of_card_four_mul_prime`); it has
    order `p` (`card_sylow_p_subgroup_of_card_four_mul_prime`). Schur–Zassenhaus then splits
    `G ≃* P ⋊[φ] K` with `|P| = p` and `|K| = 4` (`four_mul_prime_semidirectProduct`). The complement
    is then reduced to the two order-`4` possibilities, `ℤ/4` and `ℤ/2 × ℤ/2`
    (`four_mul_prime_semidirectProduct_complement_cases`), and the normal subgroup is replaced by
    the standard `CyclicRep p`, leaving actions `ℤ/4 → Aut(ℤ/p)` and
    `(ℤ/2 × ℤ/2) → Aut(ℤ/p)` (`four_mul_prime_semidirectProduct_standard_cases`). This structural
    reduction is the foundation for the full classification in `Order4P.lean`.

  * `Order4P.lean` — the **complete classification** of groups of order `4p` for odd primes `p ≥ 5`.
    Building on the Schur–Zassenhaus reduction from `Order4Prime`, the file classifies all
    semidirect products `ℤ/p ⋊ H` with `|H| = 4` by the action `φ : H → Aut(ℤ/p) ≅ (ℤ/p)ˣ`, which is
    cyclic of order `p-1`. The Sylow-2 subgroup `H` is either:

    - **Cyclic** (`H ≅ ℤ/4`): the generator acts as a unit `m` with `m⁴ = 1` in `(ℤ/p)ˣ`.
      `m = 1` gives the cyclic group `ℤ/4p` (**Type I**); `m = −1` gives the inversion semidirect
      product `ℤ/p ⋊₋₁ ℤ/4` (**Type III**); when `p ≡ 1 mod 4`, there exist `m` with `m² = −1`,
      giving `ℤ/p ⋊_m ℤ/4` (**Type IV**, only when `p ≡ 1 mod 4`).

    - **Klein four** (`H ≅ ℤ/2 × ℤ/2`): each generator maps to `±1`. If both act trivially,
      `ℤ/2 × ℤ/2p` (**Type II**). If at least one acts by inversion, `ℤ/2 × D_{2p}` (**Type V**).

    The file proves **cardinalities** (`card_fourP_I`…`card_fourP_V`), **commutativity** facts
    (`fourP_I_comm` / `fourP_II_comm` vs `fourP_III_not_comm` etc.), **pairwise non-isomorphism**
    (`fourP_I_ne_II`…`fourP_IV_ne_V`), and the two capstone theorems:
    - `fourP_classification_mod3` / `fourP_isClassif_mod3`: **4 classes** when `p ≡ 3 mod 4`
      (I, II, III, V).
    - `fourP_classification_mod1` / `fourP_isClassif_mod1`: **5 classes** when `p ≡ 1 mod 4`
      (I, II, III, IV, V), requiring a unit `c` with `c² = −1` in `(ℤ/p)ˣ`.
      Instantiated at the concrete orders **20** (`p=5`, 5 classes), **28** (`p=7`, 4 classes),
      **44** (`p=11`, 4 classes), **52** (`p=13`, 5 classes), **68** (`p=17`, 5 classes),
      **76** (`p=19`, 4 classes), **92** (`p=23`, 4 classes) in the `Classifications` decade
      subfolders (each with `classification`, `isClassif`, `numIsoClasses_eq`).

  * `Order4P_12.lean` — the **special case `p = 3`** of the `4p` classification (order **12**),
    which cannot use the `p ≥ 5` Sylow argument. When `n₃ = 1` (Sylow-3 normal), the proof
    reuses `fourP_classification_mod3_aux` (extracted from `Order4P.lean` to remove the `5 ≤ p`
    requirement) to obtain the same four types I/II/III/V. When `n₃ = 4` (Sylow-3 not normal),
    the conjugation action on the four Sylow-3 subgroups gives an injective homomorphism
    `G → S₄` whose image has index 2, hence equals `A₄` (via `eq_alternatingGroup_of_index_eq_two`).
    This yields the fifth type `fourP_A4 = alternatingGroup (Fin 4)`. The file also proves
    element-order witnesses (`fourP_III_3_has_order4`, `fourP_V_3_has_order6`), non-abelianness of
    `A₄` (`fourP_A4_not_comm`), and pairwise non-isomorphism of all five types. The capstone
    `fourP_12_isClassif` packages an `IsClassif 12`. Instantiated at `Classifications_11_to_20/Order12`.

  * `Order2PSq.lean` — the order-`2 p²` family (`p` an odd prime; the `q = 2` instance of the above),
    which has **five** classes: `ℤ/2p²`, `ℤ/p × ℤ/2p`, `D_{p²}`, `D_p × ℤ/p`, and the generalized
    dihedral `(ℤ/p)² ⋊₋₁ ℤ/2`. **Complete (sorry-free).** The five representatives are constructed with
    their orders proved `= 2p²` (`card_R1`…`card_R5`). **Distinctness** (`all_pairwise`): the five are
    pairwise non-isomorphic, assembled by `PairwiseNonMulEquiv.sum` from the abelian pair, the
    non-abelian triple (`D_{p²}` alone has an order-`p²` element, `D_p × ℤ/p` alone an order-`2p`
    element — `nonabFam_pairwise`), and one abelian-vs-non-abelian disjointness fact.
  * `Order2PSqExhaustive.lean` — **exhaustiveness, cyclic Sylow case.** `order2psq_semidirect`: every
    order-`2p²` group is `ℤ/p² ⋊[ψ] ℤ/2` or `(ℤ/p)² ⋊[ψ] ℤ/2` (via `psq_semidirectProduct` +
    `SemidirectProduct.congr'` transport + `prime_sq_classification`). `order2psq_cyclicCase`: the
    only involutions of `ℤ/p²` are `±1` (`cyclicRep_mulAut_involution`, from `k²=1 ⇒ k=±1` in `ℤ/p²`),
    giving `ℤ/2p²` (trivial action, via CRT) or `D_{p²}` (inversion, via `SemidirectProduct.lift`).
  * `Order2PSqElem.lean` — **exhaustiveness, elementary-abelian Sylow case, and the capstone.** The
    reusable engine `eigenEquiv` splits an exponent-`p` abelian group under an involution `τ` as
    `fixSubgroup τ × negSubgroup τ` (`±1`-eigenspaces, projections `x ↦ (x·τx)^t` / `x ↦ (x·(τx)⁻¹)^t`
    with `2t = p+1`); `semidirectProdSplit` peels off a factor on which the action is trivial, so
    `elem_decomp_semidirect` gives `G ≅ Fix × (Neg ⋊₋₁ ℤ/2)`. Casing on `|Neg| ∈ {1, p, p²}`
    (`order2psq_elemCase`) yields `(ℤ/p)²×ℤ/2 ≅ ℤ/p×ℤ/2p`, `ℤ/p × D_p`, or the generalized dihedral
    `(ℤ/p)² ⋊₋₁ ℤ/2`. The capstone `order2psq_classification` combines both Sylow cases: every group of
    order `2p²` is one of the five reps; with `all_pairwise` this is the full five-class theorem.
    `order2psq_isClassif` packages exhaustiveness + cards + distinctness into an `IsClassif (2p²)`.
    Instantiated at the concrete orders **18** (`p=3`), **50** (`p=5`), **98** (`p=7`) in
    `Classifications_11_to_20/Order18`, `Classifications_41_to_50/Order50`,
    `Classifications_91_to_100/Order98` (each with `classification`, `isClassif`, `numIsoClasses_eq`).

  * `PrimeSqPrimeAbelian.lean` — the order-`p²q` case with `p ∤ q − 1` **and** `q ∤ p² − 1`, where
    the group is **abelian** with exactly **two** classes: `ℤ/p²q` and `ℤ/p × ℤ/pq`. Building on
    `PrimeSqPrime` (which gives `G ≃* P ⋊[φ] K`), the key lemma `aut_eq_one_of_card_psq` shows the
    action is trivial: an automorphism `α` of the order-`p²` group `P` with `α^q = 1` is the
    identity — acting by the `q`-group `⟨α⟩`, the fixed subgroup `{x | α x = x}` has order
    `≡ p² [MOD q]` and dividing `p²` (`IsPGroup.card_modEq_card_fixedPoints`), so were `α ≠ 1` its
    order `1` or `p` would force `q ∣ p² − 1`. Hence `φ = 1` and `G ≅ P × K`, which
    `psq_prime_abelian` records is abelian. `psq_prime_abelian_classification` then splits `P` via
    `prime_sq_classification` and recombines by CRT (`crtProd`) into `ℤ/p²q` or `ℤ/p × ℤ/pq`;
    `psq_prime_distinct` separates them (cyclic vs not) and `psq_prime_isClassif` packages an
    `IsClassif (p²q)`. Instantiated at the concrete orders **45** (`p=3, q=5`) and **99**
    (`p=3, q=11`) in `Classifications_41_to_50/Order45` and `Classifications_91_to_100/Order99`
    (each with `abelian`, `classification`, `isClassif`, `numIsoClasses_eq`).

  * `PrimeSqPrimeNonabelian.lean` — the order-`3p²` case with `3 ∤ p − 1` **and** `p ≥ 5`,
    where the group has exactly **three** classes:
    `psqPrimeRep1 p q = ℤ/3p²` (cyclic), `psqPrimeRep2 p 3 = ℤ/p × ℤ/3p` (abelian non-cyclic),
    and `psqPrimeNonabRep p = (ℤ/p)² ⋊ ℤ/3` (the unique nonabelian semidirect product). The key
    lemmas `aut_eq_one_of_cyclic_psq` (when the Sylow `p`-subgroup is cyclic, the action is
    trivial) and `semidirect_elem_nonab_iso` (all non-trivial actions `ℤ/3 → Aut((ℤ/p)²)` are
    conjugate, yielding a unique nonabelian class) reduce via `psq_semidirectProduct` to the
    three-class theorem `psq_prime_nonab_classification`. `psq_prime_nonab_isClassif` packages
    an `IsClassif (p²·3)`. Instantiated at the concrete order **75** (`p=5`) in
    `Classifications_71_to_80/Order75` (with `classification`, `isClassif`,
    `numIsoClasses_eq`).

  * `P3Group/` — the classification of groups of order `p³` into five classes (`ℤ/p³`,
    `ℤ/p² × ℤ/p`, `(ℤ/p)³`, and two non-abelian groups: Heisenberg / `D₄` and `ℤ/p² ⋊ ℤ/p` / `Q₈`).
    `P3Group.classification` gives exhaustiveness; the file also supplies the cards, non-abelianness,
    and pairwise non-isomorphism facts. (Imported from a companion development.) 
    The code is from [p3group](https://github.com/lixiang90/p3group).
    
  * `AbelianPa.lean` — the exhaustiveness engine for **abelian** groups of order `p^a`, organised by
    the partitions of `a`. `partitionGroup p lam` is the group `∏ ℤ/p^λᵢ` attached to a partition
    `lam : Nat.Partition a` (indexed over its parts); `card_partitionGroup` shows it has order `p^a`,
    and `abelian_pa_classification` proves **every** abelian group of order `p^a` is `≃*
    partitionGroup p lam` for *some* partition `lam` of `a` (via the structure theorem
    `CommGroup.equiv_prod_multiplicative_zmod_of_finite`, with `exists_equiv_of_map_univ_eq` aligning
    the cyclic factors to the parts). This reduces the abelian part of any `p^a` order to enumerating
    partitions of `a`.

  * `AbelianPaUniqueness.lean` — the **injective** half, completing the correspondence. The separating
    invariant is the `p^j`-torsion count `torsionCard G (p^j) = #{x : x^(p^j) = 1}`, which for
    `partitionGroup p lam` equals `p ^ (∑ᵢ min j λᵢ)` (`torsionCard_partitionGroup`); the sequence
    `j ↦ ∑ᵢ min j λᵢ` recovers the multiset of parts (`multiset_eq_of_min_sum_eq`). Hence
    `partitionGroup_mulEquiv_iff`: `partitionGroup p lam ≃* partitionGroup p mu ↔ lam = mu`. Combined
    with exhaustiveness, `abelian_classCount` gives the genuine count: any complete, pairwise
    non-isomorphic list of abelian groups of order `p^a` has length `Nat.card (Nat.Partition a)`, the
    number of partitions of `a`. (The cyclic-factor torsion count uses
    `IsCyclic.card_powMonoidHom_ker`.)

  * `Order16_Wild.lean` — the **complete classification** of groups of order `16 = 2⁴` into
    **fourteen** classes, following Marcel Wild's "The Groups of Order Sixteen Made Easy"
    (AMM, 2005). The five abelian classes come straight from the `AbelianPa` partition engine
    (`orderP4Abel_complete`). The nine non-abelian classes are built as extensions of a normal
    `C₈` or `K₈ = C₄ × C₂` subgroup — Wild's Lemma 2 (`lemma_normal_c8_or_k8`) shows every
    non-`(C₂)⁴` group of order `16` has such a normal subgroup — classified by the conjugation
    action of a complement involution: an involution in `Aut(C₈) ≅ (ZMod 8)ˣ` gives six extension
    types (`classify_of_order8`, casing on the conjugation exponent `m ∈ {1,3,5,7}`), and one of
    the four conjugacy classes of involutions in `Aut(K₈) ≅ D₈` gives the remaining seven
    (`classify_of_k8`, casing on Wild's `ψ₁`–`ψ₈` with generators rebased to normalise the
    extension cocycle `t²`). `order16_wild_classification` (exhaustiveness), `order16_wild_distinct`
    (via the invariant tuple `(|Z(G)|, #{x²=1}, #{x⁴=1}, #squares)`, checked by `decide`), and
    `order16_wild_isClassif`. Instantiated at **16** in `Classifications_11_to_20/Order16`.

  * `Order24.lean` — the **complete classification** of groups of order `24 = 3 · 8` into
    **fifteen** classes. Sylow counting splits the proof into the normal Sylow-`3` branch
    (`C₃ ⋊ H`, with `|H| = 8`), the normal Sylow-`2` branch, and the faithful action on the four
    Sylow-`3` subgroups, which gives `S₄`. The representatives `order24_reps` are separated by the
    invariant tuple `(|Z(G)|, #{x²=1}, #{x³=1})`, giving `order24_reps_pairwise` and
    `order24_isClassif`. Instantiated at **24** in `Classifications_21_to_30/Order24`.

  * `Order54.lean` — the **complete classification** of groups of order `54 = 2 · 3³` into
    **fifteen** classes. The Sylow-`3` subgroup (order `27`) is unique and normal, so
    Schur–Zassenhaus splits `G ≅ N ⋊ C₂` with `N` one of the five order-`27` groups from
    `P3Group` (`C₂₇`, `C₉ × C₃`, `C₃³`, the Heisenberg group, and `SemidirectP2P`); the remaining
    work is an orbit calculation on the involutions of `Aut(N)` for each kernel, the hardest case
    being the Heisenberg group's non-abelian automorphism group (`order54_heisenberg_mulAut_
    center_fixed_cases`, `..._center_reversal_conj_negB`, with dozens of explicit conjugating
    automorphisms checked by `decide +kernel`). The fifteen representatives `order54_reps` split
    into `C54`, `D27`, four `Mixed` types (`C₉×C₃` kernel), four `Elem` types (`C₃³` kernel),
    three `Heis` types (Heisenberg kernel), and two `P2P` types (exponent-`9` non-abelian kernel).
    `order54_complete`, `order54_reps_pairwise` (via a center-order / element-count invariant),
    `order54_isClassif`. Instantiated at **54** in `Classifications_51_to_60/Order54`.

  * `Order84.lean` — the **complete classification** of groups of order `84 = 2² · 3 · 7` into
    **fifteen** classes. The Sylow-`7` subgroup is unique and normal, so Schur–Zassenhaus splits
    `G ≅ C₇ ⋊[φ] H` with `H` one of the five order-`12` groups from `Order4P_12` (`C₁₂`,
    `C₂ × C₆`, the dicyclic `C₃ ⋊ C₄`, `C₂ × D₆`, and `A₄`); the action
    `φ : H → Aut(C₇) ≅ (ZMod 7)ˣ` is classified per complement type by explicit case analysis on
    generator images (`order84_c12_action_cases`, `order84_c2c6_action_cases`), folding together
    Galois-conjugate/automorphism-equivalent actions (`order84_C12_mulFive`, `order84_HB_mulFive`).
    `order84_complete`, `order84_reps_pairwise` (center-order / element-count invariant),
    `order84_isClassif`, with the reduction `order84_semidirectProduct`. Instantiated at **84**
    in `Classifications_81_to_90/Order84`.

  * `Order90.lean` — the **complete classification** of groups of order `90 = 2 · 3² · 5` into
    **ten** classes. Since `90 = 2 · 45` with odd half-order, the sign of the left-regular action
    gives a normal subgroup `N` of order `45` of index `2`; Schur–Zassenhaus splits
    `G ≅ N ⋊ C₂` with `N` one of the two abelian order-`45` groups (`C45` or `C₃×C₃×C₅`, via the
    `PrimeSqPrimeAbelian`/`Order2PSq` machinery), and the involutions on `N` are classified via
    explicit unit-valued homomorphisms (`order90_c45UnitHom`). The ten representatives
    `order90_reps` include `C90`, `D45`, `C9 × D5`, `C5 × D9`, and generalized-dihedral variants
    over `C₃ × C₃ × C₅`. `order90_complete`, `order90_reps_pairwise`, `order90_isClassif`.
    Instantiated at **90** in `Classifications_81_to_90/Order90`.

  * `Order60/A5.lean` + `Order60/Semiproduct.lean` + `Order60/Classification.lean` — the
    **complete classification** of groups of order `60 = 5 · 12` into **thirteen** classes.
    Sylow-`5` counting gives `n₅ = 1` or `n₅ = 6`: `n₅ = 6` forces `G ≅ A₅` (via the faithful
    action on the six Sylow subgroups, `A5.lean`); `n₅ = 1` (`Semiproduct.lean`) makes the
    Sylow-`5` subgroup normal, so Schur–Zassenhaus splits `G ≅ ℤ/5 ⋊[φ] K` with `K` one of
    the five order-`12` types from `Order4P_12`. Since `Aut(ℤ/5) ≅ (ZMod 5)ˣ` is abelian, two
    actions give isomorphic semidirect products iff they lie in the same `Aut(K)`-orbit; pinning
    the action by case analysis on each `K` gives twelve solvable classes:
    – five direct products `ℤ/5 × K` (trivial action); for `K = ℤ/12` and `Dic₃`, two nontrivial
    actions (inversion and faithful order-4) yield four more; for `K = ℤ/2 × ℤ/6`, one
    order-2 action; for `K = ℤ/2 × D₆`, two distinct order-2 actions (through the `ℤ/2` factor
    and the dihedral sign). The thirteen representatives are separated by center cardinality
    (`60,60,10,10,5,6,3,6,2,1,1,2,1`) and, for the tied pairs, by order-`4` element witnesses
    or simplicity (`A₅`). `Classification.lean` assembles the two branches into
    `sixty_classification` (exhaustiveness) and `sixty_isClassif` (bundled `IsClassif 60`).
    Instantiated at **60** in `Classifications_51_to_60/Order60`.

  * `Order100.lean` — the **complete classification** of groups of order `100 = 2² · 5²` into
    **sixteen** classes. The Sylow-`5` subgroup (order `25`) is unique and normal
    (`card_sylow_5_eq_one_of_card_100`, `sylow_5_normal_of_card_100`), so `G ≅ P ⋊[φ] H` with
    `P ∈ {C₂₅, C₅ × C₅}` (`PrimeSqClassification`) and `H ∈ {C₄, C₂ × C₂}`; the classification is
    a `2 × 2` grid over the `(P, H)` combinations, enumerating the homomorphisms
    `φ : H → Aut(P)` up to the natural orbit equivalence for each cell. The sixteen
    representatives `order100_reps` (`order100_RA` … `order100_RP`) give `order100_complete`,
    `order100_reps_pairwise`, `order100_isClassif`. Instantiated at **100** in
    `Classifications_91_to_100/Order100`.

  * `Counting.lean` — turns exhaustiveness + distinctness into a *counting* statement. `IsClassif N
    rep` says `rep : Fin k → Type` is a complete, non-redundant list of representatives of the
    groups of order `N`; `IsClassif.card_unique` proves the length `k` is well defined, so
    exhibiting such a list of length `k` proves "there are exactly `k` isomorphism classes".
    `isClassif_one` / `isClassif_two` / `isClassif_five` are the constructors used by the per-order
    files (and `isEmpty_mulEquiv_of_comm_noncomm`: an abelian group is never `≅` a non-abelian one).
    `PairwiseNonMulEquiv rep` packages the distinctness condition (`rep i ≃* rep j → i = j`) for a
    family of groups; `PairwiseNonMulEquiv.sum` concatenates two internally-distinct families that are
    cross-disjoint, and `pairwise_disjoint_of_comm_noncomm` supplies that disjointness when one family
  is all-abelian and the other all-non-abelian — so a long list of representatives is shown distinct
  by checking each homogeneous block plus one block-vs-block fact, not every cross pair.

  * `Order2PQ.lean` — the **complete classification** of groups of order `2pq` for odd primes
    `2 < p < q`. The sign homomorphism `χ : G → ℤˣ` of the left-regular action has kernel of
    index `2` (since `|G|/2 = pq` is odd), giving a **normal subgroup `N` of order `pq`**
    (`twoPQ_normal_pq_subgroup`); Schur–Zassenhaus then writes `G ≅ N ⋊ ℤ/2`
    (`twoPQ_semidirect`). `N` is cyclic (`ℤ/pq`) or, when `p ∣ q − 1`, possibly non-abelian
    (`ℤ/q ⋊ ℤ/p`, by `classification_card_eq_prime_mul`). The progression:
    - **`¬ p ∣ q − 1`** (`twoPQ_classification_4` / `twoPQ_isClassif_4`): `N` is forced cyclic; the
      involution `b` conjugates a generator `a` by `a^k` with `k² ≡ 1 (mod pq)`, and the four
      sign-choices `k ≡ ±1 (mod p)`, `±1 (mod q)` give **4 classes** — `ℤ/2pq` (I), `D_{pq}` (II),
      `ℤ/q × D_p` (III), `ℤ/p × D_q` (IV) — recognised by `nonempty_mulEquiv_dihedral_odd` and
      `nonempty_mulEquiv_prod_dihedral`.
    - **`p ∣ q − 1`** (`twoPQ_classification_6` / `twoPQ_isClassif_6`): when `N` is cyclic the same
      four types appear (shared via `twoPQ_classif_cyclicCase`); when `N` is non-abelian, its
      characteristic normal Sylow-`q` `⟨a⟩ ⊴ G` and the involution `b` satisfy `b a b⁻¹ = a^{±1}`.
      `b` **inverts** `a` ⇒ `ℤ/q ⋊ ℤ/2p` (**VI**, via `nonempty_mulEquiv_nonabRep` with `w = yb`
      of order `2p`); `b` **centralizes** `a` ⇒ `b` is central and `G ≅ (ℤ/q ⋊ ℤ/p) × ℤ/2` (**V**),
      giving **6 classes**.
    Distinctness (`twoPQ_pairwiseDistinct_4` / `_6`) is by **center cardinality** (`2pq,1,q,p`
    resp. `2pq,1,q,p,2,1`); the only same-center pair II/VI is separated by maximal element order
    (`twoPQ_II_not_VI`: `D_{pq}` has an element of order `pq`, `ℤ/q ⋊ ℤ/2p` has none). Instantiated
    at **30, 66, 70** (4 classes) and **42, 78** (6 classes) in the `Classifications` decade
    subfolders (each with `classification`, `distinct`, `isClassif`, `numIsoClasses_eq`).

  * `Order63.lean` — the **complete classification** of groups of order `63 = 7 · 3²` into **four**
    classes. Sylow counting makes the Sylow-`7` subgroup normal (`sylow7_normal_of_card63`), so
    Schur–Zassenhaus splits `G ≅ ℤ/7 ⋊[φ] K` with `|K| = 9` (`order63_semidirect`). Casing the
    complement `K` as `ℤ/9` or `(ℤ/3)²` (via `prime_sq_classification`) and the action
    `φ : K → Aut(ℤ/7) ≅ (ℤ/7)ˣ` (cyclic of order `6`) by the order of its image gives
    `order63_classification`: `ℤ/63`, `ℤ/3 × ℤ/21`, `(ℤ/7 ⋊ ℤ/3) × ℤ/3`, and `ℤ/7 ⋊ ℤ/9`. They are
    pairwise non-isomorphic (`order63_pairwise`, separated by commutativity and by order-`9` /
    order-`21` element witnesses). Instantiated at **63** in `Classifications_61_to_70/Order63`.

  * `Order36.lean` — the **complete classification** of groups of order `36 = 4 · 3²` into
    **fourteen** classes. The normal Sylow-`3` case reuses the order-`9` kernel and order-`4`
    complement analysis (`order36_normal_reps`); the non-normal Sylow-`3` case is reduced through
    the action on Sylow subgroups and contributes exactly `C₃ × A₄` and the fiber-product type
    `A₄ ×_{C₃} C₉`. The combined representatives `order36_reps` are complete
    (`order36_complete`), pairwise non-isomorphic (`order36_reps_pairwise`), and packaged as
    `order36_isClassif`. Instantiated at **36** in `Classifications_31_to_40/Order36`.

  * `Order40.lean` — the **complete classification** of groups of order `40 = 8 · 5` into
    **fourteen** classes, reusing the order-`8`-complement machinery of `Order88`. The Sylow-`5`
    subgroup is normal (`card_sylow_5_eq_one_of_card_40`), so `G ≅ ℤ/5 ⋊[φ] H` with `|H| = 8`
    (`order40_semidirectProduct`). Casing `H` over the five groups of order `8` (via
    `P3Group.classification`) and the homomorphisms `φ : H → Aut(ℤ/5) ≅ (ℤ/5)ˣ` up to the
    `Aut H × Aut(ℤ/5)`-orbit gives the fourteen representatives `order40_reps` (five direct products
    `ℤ/5 × H` plus nine non-trivial semidirect products — more than the seven of order `88`, since
    `(ℤ/5)ˣ ≅ ℤ/4` is itself a `2`-group, so a `2`-group `H` can act with image of order `1`, `2`,
    **or** `4`): `order40_classification` (exhaustiveness), `order40_reps_pairwise` (distinctness,
    separated by the triple invariant `order40_reps_invariant` — center cardinality, `#{x : x² = 1}`,
    `#{x : x⁴ = 1}`), and `order40_isClassif`. Instantiated at **40** in
    `Classifications_31_to_40/Order40`.

  * `Order56.lean` — the **complete classification** of groups of order `56 = 8 · 7` into
    **thirteen** classes. The Sylow-`7` count gives two cases: if the Sylow `7`-subgroup is normal,
    the argument reuses the order-`8` complement/action analysis from `Order88`; if it is not
    normal, a normal subgroup of order `8` is obtained, and all `C₇`-actions are trivial except the
    single nontrivial action on `(C₂)³`. The representatives `order56_reps` are separated by the
    pair invariant `order56_reps_invariant` — center cardinality and `#{x : x² = 1}` — and packaged
    as `order56_isClassif`. Instantiated at **56** in `Classifications_51_to_60/Order56`.

  * `Order88.lean` — the **complete classification** of groups of order `88 = 8 · 11` into **twelve**
    classes. The Sylow-`11` subgroup is normal (`card_sylow_11_eq_one_of_card_88`), so
    `G ≅ ℤ/11 ⋊[φ] H` with `|H| = 8` (`order88_semidirectProduct`). Casing `H` over the five groups
    of order `8` (`C₈`, `C₄×C₂`, `(C₂)³`, `D₈`, `Q₈`, via `P3Group.classification`) and the
    homomorphisms `φ : H → Aut(ℤ/11) ≅ (ℤ/11)ˣ` (cyclic of order `10`) up to the
    `Aut H × Aut(ℤ/11)`-orbit gives the twelve representatives `order88_reps` (five direct products
    `ℤ/11 × H` plus seven non-trivial semidirect products): `order88_classification`
    (exhaustiveness), `order88_reps_pairwise` (distinctness, by center-cardinality / element-order
    invariants), and `order88_isClassif`. Instantiated at **88** in
    `Classifications_81_to_90/Order88`.


  * `Order80/` — the **complete classification** of groups of order `80 = 2⁴ · 5` into
    **fifty-two** classes, via the Sylow-`5` dichotomy (`Order80/Sylow.lean`:
    `n₅ = 1` or `n₅ = 16`).
    - **`n₅ = 1` (51 classes, `UniqueSylowFive*.lean`).** The Sylow-`5` subgroup is normal, so
      Schur–Zassenhaus splits `G ≅ C₅ ⋊[χ] K` with `K` one of the fourteen order-`16` groups
      from `Order16_Wild`; classifying the characters `χ : K →* (ZMod 5)ˣ` up to `Aut K`
      per `K`-type (`UniqueSylowFive_K1to7.lean`, `UniqueSylowFive_K0_K8to13.lean` — including
      several non-obvious merges found via automorphisms mixing the semidirect factors, and one
      genuine tie broken by a square-root-fiber-count invariant) gives
      `2+5+4+5+3+3+3+4+4+4+4+3+4+3 = 51` classes, bundled by
      `UniqueSylowFive_Summary.lean` (`order80_normal_reps`, `order80_normal_classification`).
    - **`n₅ = 16` (1 class, `SixteenSylowFive.lean`).** Counting forces the Sylow-`2` subgroup
      normal, so `G ≅ P ⋊[φ] C₅` with `|P| = 16`; the action of a `C₅`-generator is
      fixed-point-free when nontrivial (`order80_sixteen_sylow_fpf`, `fpf_of_ne_one`), and
      mod-`5` orbit counting (`mulAut_five_card_modEq`, via
      `IsPGroup.card_modEq_card_fixedPoints`) rules out `13` of the `14` order-`16` types by
      their involution (or, for `SD₁₆`, order-`8`-element) count — leaving `P = (C₂)⁴` as the
      only possibility. All nontrivial actions `φ : C₅ → Aut(C₂)⁴` are shown isomorphic via an
      explicit orbit-basis normal form (the companion automorphism of `x⁴+x³+x²+x+1`), giving
      the single class `order80_nonnormal_rep = (C₂)⁴ ⋊ C₅`.
    - `Classification.lean` bundles both branches (disjoint by the Sylow-`5`-count
      isomorphism invariant) into `order80_reps : Fin 52 → Type`, `order80_classification`,
      `order80_reps_pairwise`, `order80_classCount`, and `order80_isClassif : IsClassif 80 _`.
      Instantiated at **80** in `Classifications_71_to_80/Order80`.


  * `Order81.lean` / `Order81_CaseB.lean` — the **complete classification** of groups of
    order `81 = 3⁴` into **fifteen** classes: five abelian (via the general `ℤ/pᵃ`-abelian
    engine, one per partition of `4`) and ten non-abelian.
    - **Structural reduction (`Order81.lean`).** Every non-abelian group of order `81` has
      a normal abelian subgroup of order `27`, of type `ℤ/9 × ℤ/3` or elementary abelian
      `(ℤ/3)³`, with a non-trivial `ℤ/3`-action induced by conjugation from an outside
      element. The `(ℤ/3)³` case is closed via the full `GL(3,3)`-conjugacy classification
      of order-dividing-`3` automorphisms (identity / Jordan block / rank-`1` unipotent)
      together with a "kernel-switching" argument (a non-split rank-`1` extension over one
      elementary-abelian kernel is a *split* extension over a different one), giving
      `order81_e27_jordan_rep` and `order81_heisenberg_prod_cyclic`. The `ℤ/9 × ℤ/3` case is
      closed via a `27`-way case-bash over the parameter space of order-dividing-`3`
      automorphisms (`order81_c9c3_shear_rep`, `order81_c9c3_lift_rep`,
      `order81_c9c3_doubleShear_rep`, `order81_c9c3_sixShear_rep`,
      `order81_semidirectP2P_prod_cyclic`) plus cyclic-kernel cohomology triviality for the
      case with an element of order `27` (`order81_c27_semidirect_rep`). This leaves one
      gap: a non-split `ℤ/9 × ℤ/3`-kernel extension with no element of order `27`.
    - **The final case (`Order81_CaseB.lean`).** Given the setting above, the outside
      element's transported conjugation action is a parameter automorphism; ruling out an
      always-splitting family (`doubleShear`-conjugate actions, eliminated by contradiction)
      and reducing every surviving action to the standard `sixShear` form (via an explicit
      `liftAut`-conjugation together with an action-squaring move, plus an
      inversion-automorphism trick resolving a residual twist ambiguity) yields
      `Nonempty (G ≃* order81_c9_semidirect_c9_rep) ∨ Nonempty (G ≃* order81_c9c3_nonSplit_rep)`
      (`order81_caseB_dispatch`), built from scratch via a coset-decomposition uniqueness
      lemma and an explicit generator-relation isomorphism.
    - `order81_complete`, `order81_reps : Fin 15 → Type`, `order81_reps_pairwise`, and
      `order81_isClassif : IsClassif 81 order81_reps` assemble both branches. Instantiated
      at **81** in `Classifications_81_to_90/Order81`.

* `Smallgroups/Classifications/` — one file per order, grouped into decade subfolders
  `Classifications_1_to_10`, `Classifications_11_to_20`, …, `Classifications_91_to_100`.
  Each `OrderN.lean` proves the three classification theorems for order `N` in namespace
  `Smallgroups.Classifications.OrderN`:
  * `classification` — (1) exhaustiveness: every group of order `N` is isomorphic to a listed
    representative;
  * `distinct` — (2) distinctness: the representatives are pairwise non-isomorphic;
  * `isClassif` / `numIsoClasses_eq` — (3) counting: the count of isomorphism classes, *proved*
    from (1) and (2) via the `Counting.lean` framework (`numIsoClasses_eq` shows any complete
    non-redundant representative list has the stated length).


## Building

```sh
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build
```
