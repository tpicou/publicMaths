# Grau Ribas's cube-root conjecture (OEIS A113768)

José María Grau Ribas proposed the asymptotic formula in the OEIS entry on February 13, 2024. The recurrence itself was contributed by Jonathan Vos Post in 2006. The argument below also identifies every perfect cube in the sequence. Historical priority for the proof and the additional result is unverified. [OEIS A113768](https://oeis.org/A113768)

## Statements

Let $a_1=1$ and $a_{n+1}=a_n+\lfloor\sqrt[3]{a_n}\rfloor$ for $n\ge1$. Then

$$
\lim_{n\to\infty}\frac{a_n}{(2n/3)\sqrt{2n/3}}=1.
$$

The set of perfect cubes among the sequence values is exactly $\{8^j:j\ge0\}$. Both statements concern the infinite sequence.

The block structure below also gives a sharper expansion (proved on paper, not formalised):

$$
a_n=\left(\frac{2n}{3}\right)^{3/2}-n-\frac12\sqrt{\frac{2n}{3}}\,\log_2 n+O(\sqrt n).
$$

A complete write-up with all proofs is in [proof.pdf](proof.pdf) (source: [proof.tex](proof.tex)).

## Proof outline

Let $N_k$ be the first index for which $a_{N_k}\ge k^3$, and write $a_{N_k}=k^3+r_k$. The sequence grows by at least one and a step across the preceding cube boundary overshoots by less than $k$, so every positive block is reached. Within $[k^3,(k+1)^3)$ every step has size $k$. The width in value is $3k^2+3k+1$. Thus $r_{k+1}$ is the least nonnegative residue of $r_k-1$ modulo $k$.

When $r_k>0$ the overshoot decreases by one. When $r_k=0$ it resets to $k-1$ at the next block and reaches zero again at $2k$. Since $r_1=0$, the zero overshoots occur precisely at powers of two. Equivalently, $r_k=2^{\lceil\log_2 k\rceil}-k$. An exact cube can occur only as the first value of its block. This proves the powers-of-eight result.

The number of steps to the next block is $3k+3$ plus one precisely when $r_k=0$. Summing from block 1 to block $k-1$ gives

$$
N_k=1+\frac{3(k-1)(k+2)}2+\lceil\log_2 k\rceil.
$$

Every value in the block is $a_{N_k+j}=k^3+r_k+jk$ for $0\le j<N_{k+1}-N_k$. In particular, if $N_k\le n<N_{k+1}$ then $n\sim3k^2/2$ and $a_n\sim k^3$. Combining the two gives the conjectured limit.

## Lean verification

[CubeRoot.lean](../../Maths/GrauRibas/CubeRoot.lean) defines the one-based recurrence with mathlib's integer cube root `Nat.nthRoot 3`. mathlib documents but does not prove that this is the floor of the real cube root, so the file proves it (`nthRoot_three_eq_floor`) and restates the recurrence with $\lfloor a_n^{1/3}\rfloor$ over the reals (`a_succ`). The auxiliary value at index zero is excluded from the cube-hit theorem. A kernel-checked `decide` confirms the first 29 terms against the OEIS data; all 10,000 terms of the OEIS b-file were also matched numerically. The module is imported by the repository's default build and covered by its axiom audit.

| Declaration in `Maths.GrauRibas` | Statement |
| --- | --- |
| `a_one`, `a_succ`, `nthRoot_three_eq_floor` | The recurrence, with the real cube root, exactly as in OEIS. |
| `grauRibas_asymptotic` | The ratio above tends to one over the real numbers. |
| `cubes_are_powers_of_eight` | A natural number is both a cube and a sequence value at a positive index if and only if it is a power of eight. |
| `entry_formula`, `entry_value`, `previous_lt` | The exact index $N_k$, the value there, and the strict inequality one index earlier. |
| `block_value` | The arithmetic progression in each block, including the step into the next block. |
| `cbrt_on_block` | The cube root of $a_n$ equals $k$ exactly on the index block $[N_k, N_{k+1})$. |

From the repository root, run:

```sh
lake exe cache get
lake build Maths.GrauRibas.CubeRoot
lake env leanchecker Maths.GrauRibas.CubeRoot
```

Re-checked on 2026-11-26: the module compiles with the pinned Lean 4.34.1 and mathlib revision with no warnings, `leanchecker` passes, and every theorem audited in [Maths.lean](../../Maths.lean) depends only on `propext`, `Classical.choice` and `Quot.sound`. The $O(n^{-1/2})$ rate and the second-order expansion are not formalised.
