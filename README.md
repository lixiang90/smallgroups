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
| `7·3²` | 63 | 4 | `ℤ/63`, `ℤ/3×ℤ/21`, `(ℤ/7⋊ℤ/3)×ℤ/3`, `ℤ/7⋊ℤ/9` | `Order63` |
| `8·11` | 88 | 12 | `ℤ/11 ⋊ H` (`H` of order 8) — 12 actions | `Order88` |

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
