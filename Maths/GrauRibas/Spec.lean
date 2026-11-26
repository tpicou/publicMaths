import Maths.GrauRibas.CubeRoot

/-!
# A113768: headline results, stated without internal definitions

Every theorem in this file is about an arbitrary sequence `f : ℕ → ℕ` that satisfies the
defining recurrence of OEIS A113768 verbatim, with the real cube root:

  `f 1 = 1` and `f (n + 1) = f n + ⌊(f n)^(1/3)⌋` for `n ≥ 1`.

The value `f 0` is unconstrained. None of the auxiliary definitions of `CubeRoot.lean`
(`a`, `entry`, `offset`, `width`, `Nat.nthRoot`) occurs in these statements, so a reader only
has to trust mathlib's `Nat.floor`, `Real.rpow`, `Real.sqrt`, `Real.logb` and `Tendsto`.
-/

namespace Maths.GrauRibas.Spec

open Filter Topology

/-- Any sequence satisfying the OEIS recurrence agrees with `a` at every positive index. -/
theorem eq_a (f : ℕ → ℕ) (h1 : f 1 = 1)
    (hrec : ∀ n, 1 ≤ n → f (n + 1) = f n + ⌊(f n : ℝ) ^ ((1 : ℝ) / 3)⌋₊)
    {n : ℕ} (hn : 1 ≤ n) : f n = a n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [h1, a_one]
    · rw [hrec n hpos, a_succ hpos, ih hpos]

/-- **Grau Ribas's conjecture**: `f n / (2n/3)^{3/2} → 1`. -/
theorem grau_ribas_conjecture (f : ℕ → ℕ) (h1 : f 1 = 1)
    (hrec : ∀ n, 1 ≤ n → f (n + 1) = f n + ⌊(f n : ℝ) ^ ((1 : ℝ) / 3)⌋₊) :
    Tendsto (fun n : ℕ => (f n : ℝ) / ((2 * (n : ℝ) / 3) * Real.sqrt (2 * (n : ℝ) / 3)))
      atTop (𝓝 1) := by
  refine grauRibas_asymptotic.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [eq_a f h1 hrec hn]

/-- **Rate of convergence**: `|f n / (2n/3)^{3/2} - 1| ≤ 1800 / √n` for every `n ≥ 1`. -/
theorem rate (f : ℕ → ℕ) (h1 : f 1 = 1)
    (hrec : ∀ n, 1 ≤ n → f (n + 1) = f n + ⌊(f n : ℝ) ^ ((1 : ℝ) / 3)⌋₊)
    (n : ℕ) (hn : 1 ≤ n) :
    |(f n : ℝ) / ((2 * (n : ℝ) / 3) * Real.sqrt (2 * (n : ℝ) / 3)) - 1|
      ≤ 1800 / Real.sqrt n := by
  rw [eq_a f h1 hrec hn]
  exact ratio_bound hn

/-- **Second-order asymptotics**: for every `n ≥ 1`,
`|f n - ((2n/3)^{3/2} - n - ½ √(2n/3) log₂ n)| ≤ 320 √n`. -/
theorem second_order (f : ℕ → ℕ) (h1 : f 1 = 1)
    (hrec : ∀ n, 1 ≤ n → f (n + 1) = f n + ⌊(f n : ℝ) ^ ((1 : ℝ) / 3)⌋₊)
    (n : ℕ) (hn : 1 ≤ n) :
    |(f n : ℝ) - ((2 * (n : ℝ) / 3) * Real.sqrt (2 * (n : ℝ) / 3) - n
        - Real.sqrt (2 * (n : ℝ) / 3) * Real.logb 2 n / 2)| ≤ 320 * Real.sqrt n := by
  rw [eq_a f h1 hrec hn]
  exact second_order_bound hn

/-- **Cubes**: a natural number is a perfect cube and a term `f n` (`n ≥ 1`) iff it is a power
of `8`. -/
theorem cubes (f : ℕ → ℕ) (h1 : f 1 = 1)
    (hrec : ∀ n, 1 ≤ n → f (n + 1) = f n + ⌊(f n : ℝ) ^ ((1 : ℝ) / 3)⌋₊)
    (m : ℕ) :
    ((∃ n : ℕ, 1 ≤ n ∧ f n = m) ∧ (∃ k : ℕ, m = k ^ 3)) ↔ ∃ j : ℕ, m = 8 ^ j := by
  rw [← cubes_are_powers_of_eight m]
  constructor
  · rintro ⟨⟨n, hn, rfl⟩, hk⟩
    exact ⟨⟨n, hn, (eq_a f h1 hrec hn).symm⟩, hk⟩
  · rintro ⟨⟨n, hn, rfl⟩, hk⟩
    exact ⟨⟨n, hn, eq_a f h1 hrec hn⟩, hk⟩

/-- The recurrence has a solution (so the theorems above are not vacuous). -/
theorem exists_solution : ∃ f : ℕ → ℕ, f 1 = 1 ∧
    ∀ n, 1 ≤ n → f (n + 1) = f n + ⌊(f n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ :=
  ⟨a, a_one, fun _ hn => a_succ hn⟩

end Maths.GrauRibas.Spec
