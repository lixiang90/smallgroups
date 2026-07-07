# Report: Classification of Non-Abelian Groups of Order 81

**Source:** Thesis on the classification of non-abelian groups of order 81.

---

## 1. Key Objectives

1. Provide an **elementary proof** of the **Cyclic Extension Theorem** (without using Artin-Schreier theory).
2. Use cyclic extensions to **classify the ten non-abelian groups of order 81 = 3^4**. (There are also five abelian groups of order 81, but the thesis focuses on non-abelian ones.)

---

## 2. The Cyclic Extension Theorem

### Definition of Extension Type

Given a group \( G \) with a normal subgroup \( N \triangleleft G \) such that \( G/N \cong C_n \) (cyclic of order \( n \)):
- Pick \( a \in G - N \) where the coset \( Na \) generates \( G/N \).
- Let \( v = a^n \in N \).
- Let \( \tau \in \text{Aut}(N) \) be conjugation by \( a \).
- Then \( \tau(v) = v \), and \( \tau^n \) is conjugation by \( v \).

An **extension type** is a quadruple \((N, n, \tau, v)\) satisfying these conditions.

### Theorem 1 (Cyclic Extension Theorem)

Every extension type \((N, n, \tau, v)\) is realized by a group \( G \). The proof constructs \( G \) as ordered pairs \((x, a^i)\) with a carefully defined binary operation and proves it satisfies group axioms.

---

## 3. Construction of All Groups of Order 81

### Key Theorems Reducing \( N \)

#### Theorem 2: Every group of order \( p^4 \) has an abelian subgroup of order at least \( p^3 \).

**Proof sketch:**

1. Let \( Z = Z(G) \). If \( |Z| \ge p^3 \), done (abelian center).
2. Since \( p \)-groups have non-trivial centers, assume \( |Z| = p \) or \( p^2 \).
3. **Claim:** \( G \) has a normal subgroup \( H \) of order \( p^2 \).
   - If \( |Z| = p^2 \), take \( H = Z \).
   - If \( |Z| = p \), work in \( G/Z \). By a known lemma, it suffices to find a normal subgroup of order \( p \) in \( G/Z \):
     - If \( G/Z \) is abelian, done (its subgroups are normal).
     - If \( G/Z \) is non-abelian, its center \( Z(G/Z) \) is a non-trivial normal subgroup of order \( p \).
4. Define \( \Phi: G \to \text{Aut}(H) \) by \( \Phi(g)(h) = ghg^{-1} \). Clearly \( H \subseteq \ker(\Phi) \).
5. **By contradiction:** If \( \ker(\Phi) = H \), then \( |G/\ker(\Phi)| = p^2 \). By the First Isomorphism Theorem, \( |G/\ker(\Phi)| \) divides \( |\text{Aut}(H)| \).
   - If \( H \cong C_{p^2} \): \( |\text{Aut}(H)| = p^2 - p \), not divisible by \( p^2 \).
   - If \( H \cong C_p \times C_p \): \( |\text{Aut}(H)| = (p^2-1)(p^2-p) \), not divisible by \( p^2 \).
   - Contradiction. So \( \ker(\Phi) \) strictly contains \( H \).
6. Hence, there exists \( g \in G - H \) commuting with all elements of \( H \). Since \( H \) is abelian, \( \langle H, g \rangle \) is abelian of order at least \( p^3 \).

This justifies considering only the three abelian subgroups of order 27 as candidates for \( N \).

#### Theorem 3: If a non-abelian group of order 81 contains \( C_{27} \), it also contains \( C_9 \times C_3 \).

**Proof sketch:**

1. Let \( H = \langle h \rangle \) be cyclic of order 27 in \( G \). Pick \( a \in G - H \), define \( v = a^3 \), and let \( \tau \in \text{Aut}(H) \) act via conjugation by \( a \). Then \( G = \langle h, a \rangle \).
2. \( |\text{Aut}(H)| = \varphi(27) = 18 \). Elements of order 3 in \( \text{Aut}(H) \) are \( x \mapsto x^{10} \) (up to squaring by Lemma 2). Assume WLOG \( \tau(x) = x^{10} \).
3. Let \( H' = \langle h^3 \rangle \), a cyclic subgroup of order 9. \( H' \) commutes with \( a \) since \( \tau(h^3) = h^{30} = h^3 \), so \( ah^3 = h^3 a \).
4. **Goal:** Find \( x \in G \) with \( |x| = 3 \), \( x \notin H' \), and \( xh^3 = h^3x \). Then \( \langle h^3, x \rangle \cong C_9 \times C_3 \).
5. Let \( a' = ah^r \) with \( r \) to be determined. For any \( n \in H \), \( a'n(a')^{-1} = \tau(n) \), so \( a' \) still commutes with \( H' \).
6. Compute \( (a')^3 = N_\tau(h^r) v = h^{3r} v \) (since \( N_\tau(h^r) = h^r \cdot h^{10r} \cdot h^{100r} = h^{111r} = h^{3r} \)).
7. We need \( (a')^3 = e \), i.e., \( v = h^{-3r} \) for some \( r \). Equivalently, \( v \in H' \).
8. But \( v \) is fixed by \( \tau \), and \( H' \) is precisely the set of all fixed points of \( \tau \). Thus \( v \in H' \), and the desired \( r \) exists. \( a' \) has order 3 and commutes with \( H' \).

Hence, any non-abelian group of order 81 containing \( C_{27} \) must also contain \( C_9 \times C_3 \), so \( C_{27} \) need not be considered separately. Only two choices of \( N \) remain:
  - \( N = C_9 \times C_3 \)
  - \( N = C_3 \times C_3 \times C_3 \)

### Automorphisms \(\tau\) of Order 3 (up to conjugacy and squaring)

| \( N \) | \(\tau\) (matrix form) |
|--------|---------------------|
| \( C_9 \times C_3 \) | \(\begin{pmatrix} 1 & 3 \\ 0 & 1 \end{pmatrix}\), \(\begin{pmatrix} 4 & 0 \\ 0 & 1 \end{pmatrix}\), \(\begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}\), \(\begin{pmatrix} 1 & 3 \\ 1 & 1 \end{pmatrix}\), \(\begin{pmatrix} 1 & 6 \\ 1 & 1 \end{pmatrix}\) |
| \( C_3 \times C_3 \times C_3 \) | \(\begin{pmatrix} 1 & 1 & 0 \\ 0 & 1 & 0 \\ 0 & 0 & 1 \end{pmatrix}\), \(\begin{pmatrix} 1 & 1 & 0 \\ 0 & 1 & 1 \\ 0 & 0 & 1 \end{pmatrix}\) |

### Choosing \( v \)

The element \( v \in N \) must be fixed by \( \tau \). Using lemmas about equivalence (Lemmas 2–4), the number of distinct \( v \) choices is reduced significantly.

---

## 4. Final Classification: 10 Non-Abelian Groups

Every non-abelian group of order 81 is realized by exactly one of the following extension types \((N, 3, \tau, v)\):

### From \( N = C_9 \times C_3 \):
| # | \(\tau\) | \(v\) | Center | Elements of order 3 |
|---|---------|-------|--------|---------------------|
| 1 | \(\begin{pmatrix}1&3\\0&1\end{pmatrix}\) | \(\begin{pmatrix}0\\0\end{pmatrix}\) | \(C_9\) | 26 |
| 2 | \(\begin{pmatrix}1&3\\0&1\end{pmatrix}\) | \(\begin{pmatrix}1\\0\end{pmatrix}\) | \(C_9\) | 8 |
| 3 | \(\begin{pmatrix}4&0\\0&1\end{pmatrix}\) | \(\begin{pmatrix}0\\0\end{pmatrix}\) | \(C_3\times C_3\) | 26 |
| 4 | \(\begin{pmatrix}4&0\\0&1\end{pmatrix}\) | \(\begin{pmatrix}0\\1\end{pmatrix}\) | \(C_3\times C_3\) | 8 |
| 5 | \(\begin{pmatrix}1&0\\1&1\end{pmatrix}\) | \(\begin{pmatrix}0\\0\end{pmatrix}\) | \(C_3\times C_3\) | 26 |
| 6 | \(\begin{pmatrix}1&0\\1&1\end{pmatrix}\) | \(\begin{pmatrix}0\\1\end{pmatrix}\) | \(C_3\times C_3\) | 8 |
| 7 | \(\begin{pmatrix}1&3\\1&1\end{pmatrix}\) | \(\begin{pmatrix}0\\0\end{pmatrix}\) | \(C_3\) | 26 |
| 8 | \(\begin{pmatrix}1&6\\1&1\end{pmatrix}\) | \(\begin{pmatrix}0\\0\end{pmatrix}\) | \(C_3\) | 62 |
| 9 | \(\begin{pmatrix}1&6\\1&1\end{pmatrix}\) | \(\begin{pmatrix}3\\0\end{pmatrix}\) | \(C_3\) | 8 |

### From \( N = C_3 \times C_3 \times C_3 \):
| # | \(\tau\) | \(v\) | Center | Elements of order 3 |
|---|---------|-------|--------|---------------------|
| 10 | \(\begin{pmatrix}1&1&0\\0&1&0\\0&0&1\end{pmatrix}\) | \(\begin{pmatrix}0\\0\\0\end{pmatrix}\) | \(C_3\times C_3\) | 80 |

> Note: The 11th case (\(\tau = \begin{pmatrix}1&1&0\\0&1&1\\0&0&1\end{pmatrix}\), \(v=0\)) yields a group containing \(C_9\times C_3\) and is equivalent to a previously listed case via Lemma 8/9.

---

## 5. Key Techniques Used

- **Cyclic Extension Theorem:** Elementary construction of groups from extension types.
- **Reduction of \(N\):** Theorems 2 and 3 show only abelian subgroups of order 27 need be considered, and \(C_{27}\) can be excluded.
- **Equivalence Lemmas:** Lemmas 1–4 reduce the number of extension types to consider (conjugacy, squaring of \(v\), change of generator via \(N_\tau\)).
- **Matrix Representation:** Automorphisms of \(C_9\times C_3\) and \(C_3^3\) are represented as matrices in \(GL_2(\mathbb{F}_3)\) and \(GL_3(\mathbb{F}_3)\).
- **Isomorphism Problem:** Resolved by comparing centers and counting elements of order 3.

---

## 6. References

1. Fraleigh, *A First Course in Abstract Algebra* (1967)
2. Wild, *The Groups of Order Sixteen Made Easy*, Amer. Math. Monthly (2005)
3. Hölder, *Bildung zusammengesetzter Gruppen*, Math. Ann. (1895)
4. Dummit & Foote, *Abstract Algebra*, 2nd ed. (1999)
