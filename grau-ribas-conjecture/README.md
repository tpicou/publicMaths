# Grau Ribas's conjecture for OEIS A113768 — proved and verified in Lean

The sequence [A113768](https://oeis.org/A113768) is defined by

$$
a_1=1,\qquad a_{n+1}=a_n+\left\lfloor\sqrt[3]{a_n}\right\rfloor \quad (n\ge1),
$$

and begins $1, 2, 3, 4, 5, 6, 7, 8, 10, 12, \dots, 28, 31, 34, \dots$
On February 13, 2024, José María Grau Ribas conjectured in the OEIS entry that $a_n \sim (2n/3)^{3/2}$.
This folder contains a complete proof of that conjecture, three further results, and a machine-checked Lean 4 verification of all of them.

**Start here: [proof.pdf](proof.pdf)** (5 pages, with full proofs).

## In this folder

Everything for this result is here; the folder is a self-contained Lean project.

| File | What it is |
| --- | --- |
| [proof.pdf](proof.pdf) | The write-up: statements, complete proofs, and how they map to the Lean code. |
| [proof.tex](proof.tex) | LaTeX source of the PDF. |
| [GrauRibas/Spec.lean](GrauRibas/Spec.lean) | **The Lean statements to read.** The headline theorems for any sequence satisfying the OEIS recurrence. |
| [GrauRibas/CubeRoot.lean](GrauRibas/CubeRoot.lean) | The Lean proofs. |
| [GrauRibas.lean](GrauRibas.lean) | Build entry point and axiom audit. |
| [lakefile.lean](lakefile.lean), [lake-manifest.json](lake-manifest.json), [lean-toolchain](lean-toolchain) | Lean project settings, with Lean and mathlib pinned. |

## Results

**1. Grau Ribas's conjecture, with a rate.**

$$
\lim_{n\to\infty}\frac{a_n}{(2n/3)^{3/2}}=1,
\qquad\text{and}\qquad
\left|\frac{a_n}{(2n/3)^{3/2}}-1\right|\le\frac{1800}{\sqrt n}\quad\text{for every } n\ge1.
$$

**2. Second-order expansion.** For every $n\ge1$,

$$
\left|\,a_n-\left(\left(\frac{2n}{3}\right)^{3/2}-n-\frac12\sqrt{\frac{2n}{3}}\,\log_2 n\right)\right|\le 320\sqrt n .
$$

**3. Cubes.** The perfect cubes in the sequence are exactly the powers of $8$.

**4. Exact structure.** On the range $[k^3,(k+1)^3)$ the sequence is an arithmetic progression with step $k$. It starts at $k^3+2^{\lceil\log_2 k\rceil}-k$, at the index

$$
N_k=1+\frac{3(k-1)(k+2)}{2}+\lceil\log_2 k\rceil .
$$

The constants $1800$ and $320$ come from the formal proof and are far from optimal. Numerically, the error in result 2 stays between $2.7\sqrt n$ and $3.2\sqrt n$ for $10^3\le n\le10^8$.

## The idea in brief

Let $N_k$ be the first index with $a_{N_k}\ge k^3$, and let $r_k=a_{N_k}-k^3$ be the overshoot.
While $a_n\in[k^3,(k+1)^3)$, every step adds exactly $k$, so $r_{k+1}\equiv r_k-1 \pmod k$.
The overshoot therefore decreases by one per block until it hits $0$. It then resets to $k-1$, and this happens exactly when $k$ is a power of two.
This gives $r_k=2^{\lceil\log_2 k\rceil}-k$ and the formula for $N_k$ above.
All four results follow, because $n\approx\tfrac32k^2$ and $a_n\approx k^3$ on block $k$.
A cube $k^3$ can only appear as the first term of its block, which requires $r_k=0$.

## Lean verification

The headline statements in [Spec.lean](GrauRibas/Spec.lean) are about an **arbitrary** `f : ℕ → ℕ` with `f 1 = 1` and `f (n+1) = f n + ⌊(f n : ℝ) ^ (1/3 : ℝ)⌋₊` for `n ≥ 1`.
That hypothesis is the OEIS definition word for word, with the real cube root.
The statements use none of the development's own definitions.
To trust them you only need to read that file and mathlib's definitions of floor, real powers, `Real.sqrt`, `Real.logb` and `Tendsto`.

| `GrauRibas.Spec` | Statement |
| --- | --- |
| `grau_ribas_conjecture` | $f(n)/\bigl((2n/3)\sqrt{2n/3}\bigr)\to1$ |
| `rate` | $\lvert f(n)/((2n/3)\sqrt{2n/3})-1\rvert\le1800/\sqrt n$ for $n\ge1$ |
| `second_order` | $\lvert f(n)-((2n/3)\sqrt{2n/3}-n-\tfrac12\sqrt{2n/3}\log_2 n)\rvert\le320\sqrt n$ for $n\ge1$ |
| `cubes` | $m$ is a cube and some $f(n)$ with $n\ge1$ $\iff$ $m=8^j$ |
| `exists_solution` | Such an $f$ exists, so the statements are not vacuous |

<details>
<summary>Supporting declarations in <code>GrauRibas</code></summary>

| Declaration | Statement |
| --- | --- |
| `a_one`, `a_succ`, `nthRoot_three_eq_floor` | The concrete sequence `a` satisfies the OEIS recurrence. This includes a proof that mathlib's `Nat.nthRoot 3` is the floor of the real cube root, which mathlib documents but does not prove. |
| `entry_value`, `block_value` | The arithmetic progression on each block. |
| `cbrt_on_block`, `previous_lt` | The cube root of $a_n$ is $k$ exactly on $[N_k,N_{k+1})$. |
| `entry_formula` | The closed form of $N_k$. |
| `cubes_are_powers_of_eight` | Result 3. |
| `grauRibas_asymptotic`, `ratio_bound`, `second_order_bound` | Results 1 and 2. |

A kernel-checked `decide` also confirms the first 29 terms against the OEIS data.
</details>

### Reproduce

You need [elan](https://github.com/leanprover/elan); it installs the pinned Lean 4.34.1 automatically.

```sh
git clone https://github.com/tpicou/publicMaths
cd publicMaths/grau-ribas-conjecture
lake exe cache get
lake build
lake env leanchecker --fresh GrauRibas
```

### Audit (2026-11-26)

- Builds with the pinned Lean 4.34.1 and mathlib revision, with no warnings.
- The project contains no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `opaque`, custom syntax or `set_option`. The default heartbeat limit is kept, and `autoImplicit` is off.
- Every theorem listed in [GrauRibas.lean](GrauRibas.lean) depends only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. The 29-term check depends on no axioms.
- `leanchecker --fresh` re-checks the whole development, and every mathlib declaration it uses, in Lean's kernel.
- Numerically, the recurrence reproduces all 10,000 terms of the OEIS b-file. The formulas for $N_k$ and $a_{N_k}$ agree on all 1,412 complete blocks in the first $3\times10^6$ terms.

## History

The sequence was contributed to the OEIS by Jonathan Vos Post (January 19, 2006). The conjecture was added by José María Grau Ribas (February 13, 2024). The OEIS entry records no proof. We have not checked the wider literature, so priority for the proof is unverified.
