# smallgroups

Formalizing the classification of small finite groups in **Lean 4 + Mathlib**.

## Goal

For each small order `n`, a *full classification* of groups of order `n` consists of three
theorems:

1. **Exhaustiveness** — exhibit all possible isomorphism classes and prove every group of
   order `n` is one of them.
2. **Counting** — count the isomorphism classes.
3. **Distinctness** — prove the listed classes are pairwise non-isomorphic.

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

  Done so far: order `1` (trivial group); every prime order `≤ 100` (`2, 3, 5, 7, …, 97`), each
  the single class `ℤ/N`; the prime-square orders `4, 9, 25, 49`, each with two classes `ℤ/N` and
  `ℤ/p × ℤ/p`; and the cyclic-only products `p * q` with `q ∤ p - 1`
  (`15, 33, 35, 51, 65, 69, 77, 85, 87, 91, 95`), each the single class `ℤ/N`; and the
  even products `2p` (`6, 10, 14, 22, 26, 34, 38, 46, 58, 62, 74, 82, 86, 94`), each with two
  classes `ℤ/2p` and `DihedralGroup p`; the odd products `pq` with `q ∣ p - 1`
  (`21, 39, 55, 57, 93`), each with two classes `ℤ/pq` and the non-abelian `ℤ/p ⋊ ℤ/q`; the
  prime-cubes `8` and `27`, each with five classes (via `P3Group`); and `2p^2` case (`18, 50, 98`) each with five classes.

## Building

```sh
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build
```
