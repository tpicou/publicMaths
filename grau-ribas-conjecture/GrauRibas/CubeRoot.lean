import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The cube-root recurrence A113768, indexed from 1. -/
namespace GrauRibas

/-- The auxiliary value at zero is outside the OEIS sequence. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => a (n + 1) + Nat.nthRoot 3 (a (n + 1))

private theorem step {n : ℕ} (hn : 0 < n) :
    a (n+1) = a n + Nat.nthRoot 3 (a n) := by
  cases n <;> first | rfl | omega

/-- mathlib documents, but does not prove, that `Nat.nthRoot 3` is the floor of the
real cube root. This ties the definition of `a` to the OEIS recurrence. -/
theorem nthRoot_three_eq_floor (m : ℕ) :
    Nat.nthRoot 3 m = ⌊(m : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
  set k := Nat.nthRoot 3 m
  have hlo : k^3 ≤ m := Nat.pow_nthRoot_le (.inl (by decide))
  have hhi : m < (k+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) m
  have key (x : ℝ) (hx : 0 ≤ x) : (x^3) ^ ((1 : ℝ) / 3) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  symm
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · calc (k : ℝ) = ((k : ℝ)^3) ^ ((1 : ℝ) / 3) := (key _ (by positivity)).symm
      _ ≤ (m : ℝ) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlo) (by norm_num)
  · calc (m : ℝ) ^ ((1 : ℝ) / 3) < (((k : ℝ) + 1)^3) ^ ((1 : ℝ) / 3) :=
          Real.rpow_lt_rpow (by positivity) (by exact_mod_cast hhi) (by norm_num)
      _ = k + 1 := key _ (by positivity)

/-- The initial value of A113768. -/
theorem a_one : a 1 = 1 := rfl

/-- The defining recurrence of A113768, stated with the real cube root. -/
theorem a_succ {n : ℕ} (hn : 0 < n) :
    a (n+1) = a n + ⌊(a n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
  rw [step hn, nthRoot_three_eq_floor]

/-- The first 29 terms agree with the OEIS data, checked by the kernel. -/
example : (List.range 29).map (fun i => a (i+1)) =
    [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28,
     31, 34, 37, 40, 43, 46, 49, 52, 55, 58, 61] := by
  decide +kernel

private theorem self_le (n : ℕ) : n ≤ a n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rcases n with _ | n
    · decide
    · rw [step (by omega)]
      have h : 1 ≤ Nat.nthRoot 3 (a (n+1)) :=
        (Nat.le_nthRoot_iff (by decide)).2 (by simpa using (show 1 ≤ a (n+1) by omega))
      omega

private theorem a_strict : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  rcases n with _ | n
  · decide
  · rw [step (n := n+1) (by omega)]
    have h : 1 ≤ Nat.nthRoot 3 (a (n+1)) :=
      (Nat.le_nthRoot_iff (by decide)).2 (by simpa using (show 1 ≤ a (n+1) by have := self_le (n+1); omega))
    omega

def offset (k : ℕ) := 2 ^ Nat.clog 2 k - k

private def extra (k : ℕ) := if 2 ^ Nat.clog 2 k = k then 1 else 0

def width (k : ℕ) := 3*k + 3 + extra k

/-- First index in the block starting at k cubed, for positive k. -/
def entry : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k+2 => entry (k+1) + width (k+1)

private theorem entry_succ {k : ℕ} (hk : 0 < k) : entry (k+1) = entry k + width k := by
  cases k <;> first | rfl | omega

private theorem entry_pos {k : ℕ} (hk : 0 < k) : 0 < entry k := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero => decide
    | succ k => rw [entry_succ (by omega)]; unfold width; omega

private theorem next_clog {k : ℕ} (hk : 0 < k) :
    Nat.clog 2 (k+1) = Nat.clog 2 k + extra k := by
  unfold extra
  split_ifs with h
  · have h₁ := (Nat.clog_lt_clog_succ_iff (by decide : 1 < 2)).2 h
    have h₂ : Nat.clog 2 (k+1) ≤ Nat.clog 2 k + 1 := by
      apply Nat.clog_le_of_le_pow
      rw [pow_succ, h]
      omega
    omega
  · simpa using ((Nat.clog_eq_clog_succ_iff (by decide : 1 < 2)).2 h).symm

private theorem offset_lt {k : ℕ} (hk : 0 < k) : offset k < k := by
  by_cases h : k = 1
  · subst k; decide
  have hpos := Nat.clog_pos (by decide : 1 < 2) (show 1 < k by omega)
  have H := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (show 1 < k by omega)
  have he : Nat.clog 2 k = (Nat.clog 2 k).pred + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
  unfold offset
  conv_lhs => lhs; rw [he, pow_succ]
  omega

private theorem boundary {k : ℕ} (hk : 0 < k) :
    k^3 + offset k + width k * k = (k+1)^3 + offset (k+1) := by
  have hle := Nat.le_pow_clog (by decide : 1 < 2) k
  unfold offset width
  rw [next_clog hk]
  unfold extra
  split_ifs with h
  · simp only [pow_succ, h, Nat.sub_self, Nat.add_zero]
    have he : k*2-(k+1)+1 = k := by omega
    nlinarith
  · simp only [Nat.add_zero]
    have he : 2^Nat.clog 2 k - (k+1) +1 = 2^Nat.clog 2 k - k := by omega
    nlinarith

private theorem next_offset_lt {k : ℕ} (hk : 0 < k) : offset (k+1) < k := by
  have hle := Nat.le_pow_clog (by decide : 1 < 2) k
  have hprev := offset_lt hk
  unfold offset at *
  rw [next_clog hk]
  unfold extra
  split_ifs with h
  · rw [pow_succ, h]; omega
  · simp only [Nat.add_zero]; omega

private theorem walk {k : ℕ} (hk : 0 < k) (start : a (entry k) = k^3+offset k)
    (j : ℕ) (hj : j ≤ width k) : a (entry k + j) = k^3 + offset k + j*k := by
  induction j with
  | zero => simpa using start
  | succ j ih =>
    rw [← Nat.add_assoc, step (by have := entry_pos hk; omega), ih (by omega)]
    have hu : k^3 + offset k + j*k < (k+1)^3 := by
      have hmul := Nat.mul_le_mul_right k hj
      have hb := boundary hk
      have hbetter := next_offset_lt hk
      nlinarith
    rw [Nat.nthRoot_eq_of_le_of_lt (by omega : k^3 ≤ k^3 + offset k + j*k) hu]
    ring

theorem entry_value {k : ℕ} (hk : 0 < k) : a (entry k) = k^3 + offset k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases k with _ | k
    · decide
    · have hp : 0 < k+1 := by omega
      rw [entry_succ hp, walk hp (ih hp) _ le_rfl, boundary hp]

theorem block_value {k : ℕ} (hk : 0 < k) (j : ℕ) (hj : j ≤ width k) :
    a (entry k + j) = k^3 + offset k + j*k := walk hk (entry_value hk) j hj

/-- The integer cube root of `a n` is `k` exactly on the index block `[entry k, entry (k+1))`. -/
theorem cbrt_on_block {k n : ℕ} (hk : 0 < k) (h₁ : entry k ≤ n) (h₂ : n < entry (k+1)) :
    Nat.nthRoot 3 (a n) = k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h₁
  rw [entry_succ hk] at h₂
  have hj : j + 1 ≤ width k := by omega
  rw [block_value hk j (by omega)]
  apply Nat.nthRoot_eq_of_le_of_lt (Nat.le_add_right_of_le (Nat.le_add_right _ _))
  have hmul := Nat.mul_le_mul_right k hj
  have hb := boundary hk
  have hbetter := next_offset_lt hk
  nlinarith

theorem entry_formula {k : ℕ} (hk : 0 < k) :
    2 * entry k + 4 = 3*k^2 + 3*k + 2*Nat.clog 2 k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases k with _ | k
    · decide
    · have hp : 0 < k+1 := by omega
      have H := ih hp
      rw [entry_succ hp, next_clog hp]
      unfold width
      nlinarith

theorem previous_lt {k : ℕ} (hk : 0 < k) : a (entry k - 1) < k^3 := by
  rcases k with _ | k
  · omega
  rcases k with _ | k
  · decide
  let b := k+1
  have hb : 0 < b := by dsimp [b]; omega
  change a (entry (b+1) - 1) < (b+1)^3
  rw [entry_succ hb]
  have hw : 0 < width b := by unfold width; omega
  rw [show entry b + width b - 1 = entry b + (width b - 1) by omega,
      block_value hb _ (by omega)]
  have off := next_offset_lt hb
  have he := boundary hb
  have hm := congrArg (· * b) (show width b - 1 + 1 = width b by omega)
  nlinarith

theorem cube_hit_iff {k : ℕ} (hk : 0 < k) :
    (∃ n : ℕ, 0 < n ∧ a n = k^3) ↔ ∃ j : ℕ, k = 2^j := by
  constructor
  · rintro ⟨n, _, hn⟩
    have hlo : entry k ≤ n := by
      by_contra! h
      have hm := a_strict.monotone (show n ≤ entry k - 1 by omega)
      have := previous_lt hk
      omega
    have hm := a_strict.monotone hlo
    rw [entry_value hk, hn] at hm
    have hle := Nat.le_pow_clog (by decide : 1 < 2) k
    exact ⟨Nat.clog 2 k, by unfold offset at hm; omega⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, entry_pos hk, by rw [entry_value hk]; simp [offset, Nat.clog_pow _ _ (by decide : 1 < 2)]⟩

/-- The perfect cubes occurring at positive indices are exactly the powers of eight. -/
theorem cubes_are_powers_of_eight (m : ℕ) :
    ((∃ n : ℕ, 0 < n ∧ a n = m) ∧ (∃ k : ℕ, m = k^3)) ↔ ∃ j : ℕ, m = 8^j := by
  have powers (j : ℕ) : ((2:ℕ)^j)^3 = 8^j := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    rfl
  constructor
  · rintro ⟨⟨n, hn, he⟩, k, rfl⟩
    have hk : 0 < k := by
      by_contra! h
      have hz : k = 0 := by omega
      have := self_le n
      simp [hz] at he
      omega
    obtain ⟨j, rfl⟩ := (cube_hit_iff hk).1 ⟨n, hn, he⟩
    exact ⟨j, powers j⟩
  · rintro ⟨j, rfl⟩
    rw [← powers j]
    exact ⟨(cube_hit_iff (k := 2^j) (by positivity)).2 ⟨j, rfl⟩, ⟨2^j, rfl⟩⟩

private def block (n : ℕ) := Nat.nthRoot 3 (a n)

private theorem position {n : ℕ} (hn : 0 < n) :
    0 < block n ∧ 3*(block n)^2 ≤ 2*n+4 ∧ 2*n ≤ 3*(block n)^2+11*block n+8 := by
  let k := block n
  have hk : 1 ≤ k := (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).2
    (by simpa using (show 1 ≤ a n by have := self_le n; omega))
  have hlo : k^3 ≤ a n := Nat.pow_nthRoot_le (.inl (by decide : 3 ≠ 0))
  have hhi : a n < (k+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hi : n < entry (k+1) := by
    by_contra! h
    have H := a_strict.monotone h
    rw [entry_value (by omega)] at H
    omega
  have lo : entry k ≤ n := by
    by_contra! h
    have H := a_strict.monotone (show n ≤ entry k - 1 by omega)
    have := previous_lt hk
    omega
  have hlog : Nat.clog 2 (k+1) ≤ k+1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < 2)).le
  have h₁ := entry_formula hk
  have h₂ := entry_formula (show 0 < k+1 by omega)
  change 0 < k ∧ 3*k^2 ≤ 2*n+4 ∧ 2*n ≤ 3*k^2+11*k+8
  exact ⟨hk, by omega, by nlinarith⟩

open Filter Topology

/-- Grau Ribas's conjecture, as a real ratio tending to one. -/
theorem grauRibas_asymptotic :
    Tendsto (fun n : ℕ => (a n : ℝ) / ((2*(n:ℝ)/3) * Real.sqrt (2*(n:ℝ)/3)))
      atTop (𝓝 1) := by
  let K := fun n : ℕ => (block n : ℝ)
  have hb : Tendsto block atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b^3)] with n hn
    exact (Nat.le_nthRoot_iff (by decide)).2 (hn.trans (self_le n))
  have h0 : Tendsto (fun n => 1 / K n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hb
  let u := fun n : ℕ => (a n : ℝ) / K n ^ 3
  let v := fun n : ℕ => (2*(n:ℝ)/3) / K n ^ 2
  have hu : Tendsto u atTop (𝓝 1) := by
    have htop : Tendsto (fun n => (1 + 1 / K n)^3) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow 3
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ => 1) tendsto_const_nhds htop
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
      have hk : 0 < K n := by dsimp only [K]; exact_mod_cast (position hn).1
      apply (le_div_iff₀ (pow_pos hk 3)).2
      simp only [one_mul]
      dsimp only [K, block]
      exact_mod_cast (Nat.pow_nthRoot_le (a := a n) (.inl (by decide : 3 ≠ 0)))
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
      have hk : 0 < K n := by dsimp only [K]; exact_mod_cast (position hn).1
      have H : (a n : ℝ) ≤ (K n + 1)^3 := by
        dsimp only [K, block]
        exact_mod_cast (Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) (a n)).le
      dsimp only [u]
      apply (div_le_iff₀ (pow_pos hk 3)).2
      convert H using 1; field_simp
  have hv : Tendsto v atTop (𝓝 1) := by
    have hl : Tendsto (fun n => 1 - 2 * (1 / K n)) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub ((tendsto_const_nhds (x := (2:ℝ))).mul h0))
    have hh : Tendsto (fun n => 1 + 7 * (1 / K n)) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).add ((tendsto_const_nhds (x := (7:ℝ))).mul h0))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hh
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
      obtain ⟨hp, hlow, _⟩ := position hn
      have hk : (1:ℝ) ≤ K n := by dsimp only [K]; exact_mod_cast (show 1 ≤ block n from hp)
      have hpos : 0 < K n := by linarith
      have H : 3*K n^2 ≤ 2*(n:ℝ)+4 := by dsimp only [K]; exact_mod_cast hlow
      dsimp only [v]
      apply (le_div_iff₀ (pow_pos hpos 2)).2
      rw [show (1 - 2*(1/K n))*K n^2 = K n^2-2*K n by field_simp]
      linarith
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
      obtain ⟨hp, _, hhigh⟩ := position hn
      have hk : (1:ℝ) ≤ K n := by dsimp only [K]; exact_mod_cast (show 1 ≤ block n from hp)
      have hpos : 0 < K n := by linarith
      have H : 2*(n:ℝ) ≤ 3*K n^2+11*K n+8 := by dsimp only [K]; exact_mod_cast hhigh
      dsimp only [v]
      apply (div_le_iff₀ (pow_pos hpos 2)).2
      rw [show (1 + 7*(1/K n))*K n^2 = K n^2+7*K n by field_simp]
      linarith
  have hs : Tendsto (fun n => Real.sqrt (v n)) atTop (𝓝 1) := by simpa using hv.sqrt
  have hquot := hu.div (hv.mul hs) (by norm_num : (1:ℝ)*1 ≠ 0)
  apply (show Tendsto (fun n => u n / (v n * Real.sqrt (v n))) atTop (𝓝 1) by simpa [Pi.div_def] using hquot).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hk : 0 < K n := by dsimp only [K]; exact_mod_cast (position hn).1
  dsimp only [u, v]
  rw [Real.sqrt_div (by positivity), Real.sqrt_sq hk.le]
  field_simp

/-! ## Explicit error terms -/

private theorem width_le (k : ℕ) : width k ≤ 3*k + 4 := by
  unfold width extra; split_ifs <;> omega

/-- Every positive index lies in some block `[entry k, entry k + width k)`. -/
private theorem decompose {n : ℕ} (hn : 0 < n) :
    ∃ k j, 0 < k ∧ j < width k ∧ n = entry k + j := by
  let k := block n
  have hk : 1 ≤ k := (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).2
    (by simpa using (show 1 ≤ a n by have := self_le n; omega))
  have hlo : k^3 ≤ a n := Nat.pow_nthRoot_le (.inl (by decide : 3 ≠ 0))
  have hhi : a n < (k+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hi : n < entry (k+1) := by
    by_contra! h
    have H := a_strict.monotone h
    rw [entry_value (by omega)] at H
    omega
  have lo : entry k ≤ n := by
    by_contra! h
    have H := a_strict.monotone (show n ≤ entry k - 1 by omega)
    have := previous_lt hk
    omega
  rw [entry_succ hk] at hi
  exact ⟨k, n - entry k, hk, by omega, by omega⟩

/-- A polynomial bound used for the cube of `√x`. -/
private theorem cubic_bound (K s : ℝ) (hK : 1 ≤ K) (hs1 : -1/3 ≤ s) (hs2 : s ≤ 5*K) :
    |3/4*K^2*s^2 + s^3| ≤ 145*K^4 := by
  have hK0 : 0 ≤ K := by linarith
  have hs_sq : s^2 ≤ 25*K^2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hs2) (by linarith : 0 ≤ s + 5*K)]
  have a1 : s^3 ≤ 5*K*s^2 := by nlinarith [mul_nonneg (sub_nonneg.2 hs2) (sq_nonneg s)]
  have a2 : 5*K*s^2 ≤ 125*K^3 := by
    nlinarith [mul_le_mul_of_nonneg_left hs_sq (by linarith : (0:ℝ) ≤ 5*K)]
  have a3 : K^3 ≤ K^4 := by nlinarith [pow_nonneg hK0 3]
  have a4 : K^2*s^2 ≤ 25*K^4 := by
    nlinarith [mul_le_mul_of_nonneg_left hs_sq (sq_nonneg K)]
  have a5 : -1 ≤ s^3 := by
    have : 0 ≤ (s+1)*((s-1/2)^2 + 3/4) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  have a6 : 0 ≤ K^2*s^2 := by positivity
  have a7 : 1 ≤ K^4 := one_le_pow₀ hK
  rw [abs_le]; constructor <;> linarith

/-- With `x = K^2 + s`, `x^{3/2}` is within `290 K` of `K^3 + (3/2) K s`, and at least `K^3/2`. -/
private theorem sqrt_cube_bound (K s : ℝ) (hK : 1 ≤ K) (hs1 : -1/3 ≤ s) (hs2 : s ≤ 5*K) :
    K^3/2 ≤ (K^2+s) * Real.sqrt (K^2+s) ∧
      |(K^2+s) * Real.sqrt (K^2+s) - (K^3 + 3/2*K*s)| ≤ 290*K := by
  have hK0 : 0 ≤ K := by linarith
  have hK2 : 1 ≤ K^2 := one_le_pow₀ hK
  have hxpos : 0 ≤ K^2 + s := by linarith
  set y := Real.sqrt (K^2 + s)
  have hy2 : y^2 = K^2 + s := Real.sq_sqrt hxpos
  have hyl : 4/5*K ≤ y := (Real.le_sqrt (by linarith) hxpos).2 (by nlinarith)
  set P := K^3 + 3/2*K*s with hP
  have hprod : ((K^2+s)*y - P) * ((K^2+s)*y + P) = 3/4*K^2*s^2 + s^3 := by
    have h : ((K^2+s)*y)^2 = (K^2+s)^3 := by rw [mul_pow, hy2]; ring
    rw [hP]; linear_combination h
  have hy3 : K^3/2 ≤ (K^2+s)*y := by
    have h1 : 2/3*K^2 ≤ K^2 + s := by linarith
    have h2 : 0 ≤ K^3 := by positivity
    calc K^3/2 ≤ (2/3*K^2) * (4/5*K) := by ring_nf; linarith
      _ ≤ (K^2+s)*y := mul_le_mul h1 hyl (by positivity) hxpos
  have hP0 : 0 ≤ P := by
    have h1 : -1/3*K ≤ K*s := by nlinarith
    have h2 : K ≤ K^3 := by nlinarith
    rw [hP]; linarith
  have hden : K^3/2 ≤ (K^2+s)*y + P := by linarith
  have hpos : 0 < K^3/2 := by positivity
  have e1 : |(K^2+s)*y - P| * ((K^2+s)*y + P) = |3/4*K^2*s^2 + s^3| := by
    rw [← hprod, abs_mul, abs_of_pos (by linarith : 0 < (K^2+s)*y + P)]
  have e2 : |(K^2+s)*y - P| * (K^3/2) ≤ 290*K * (K^3/2) := by
    calc |(K^2+s)*y - P| * (K^3/2) ≤ |(K^2+s)*y - P| * ((K^2+s)*y + P) :=
          mul_le_mul_of_nonneg_left hden (abs_nonneg _)
      _ = |3/4*K^2*s^2 + s^3| := e1
      _ ≤ 145*K^4 := cubic_bound K s hK hs1 hs2
      _ = 290*K * (K^3/2) := by ring
  exact ⟨hy3, le_of_mul_le_mul_right e2 hpos⟩

/-- `log₂ n` is within `O(1)` of `2 log₂ K` when `K^2 ≤ n ≤ 9 K^2`. -/
private theorem log_bounds (K m : ℝ) (hK : 1 ≤ K) (h1 : K^2 ≤ m) (h2 : m ≤ 9*K^2) :
    2 * Real.logb 2 K ≤ Real.logb 2 m ∧ Real.logb 2 m ≤ 2 * Real.logb 2 K + 4 := by
  have hKpos : 0 < K := by linarith
  constructor
  · calc 2 * Real.logb 2 K = Real.logb 2 (K^2) := by rw [Real.logb_pow]; push_cast; ring
      _ ≤ Real.logb 2 m := Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
  · calc Real.logb 2 m ≤ Real.logb 2 ((2:ℝ)^4 * K^2) :=
          Real.logb_le_logb_of_le (by norm_num) (by nlinarith) (by nlinarith)
      _ = 2 * Real.logb 2 K + 4 := by
          rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow, Real.logb_pow,
            Real.logb_self_eq_one (by norm_num)]; push_cast; ring

/-- The real-variable estimate behind `core`. Here `K` is a block number, `J` the position inside
the block, `R` the overshoot, `N` the entry index and `C = ⌈log₂ K⌉`. -/
private theorem real_core (K C J R N : ℝ) (hK : 1 ≤ K) (hR0 : 0 ≤ R) (hR' : R < K)
    (hJ0 : 0 ≤ J) (hJ' : J + 1 ≤ 3*K + 4) (hC0 : 0 ≤ C) (hCK : C ≤ K)
    (hE' : 2*N + 4 = 3*K^2 + 3*K + 2*C)
    (hl1 : Real.logb 2 K ≤ C) (hl2 : C < Real.logb 2 K + 1) :
    K^2 ≤ N + J ∧ N + J ≤ 9*K^2 ∧
      K^3/2 ≤ (2*(N+J)/3) * Real.sqrt (2*(N+J)/3) ∧
      |K^3 + R + J*K - (2*(N+J)/3) * Real.sqrt (2*(N+J)/3)| ≤ 296*K^2 ∧
      |K^3 + R + J*K - ((2*(N+J)/3) * Real.sqrt (2*(N+J)/3) - (N+J)
          - Real.sqrt (2*(N+J)/3) * Real.logb 2 (N+J) / 2)| ≤ 312*K := by
  have hK0 : 0 ≤ K := by linarith
  have hK2 : 1 ≤ K^2 := one_le_pow₀ hK
  have hKK : K ≤ K^2 := by nlinarith
  -- `x = 2n/3 = K^2 + s`, with `s` of size `O(K)`
  set s := K + (2*C - 4 + 2*J)/3 with hs
  have hx : 2*(N+J)/3 = K^2 + s := by rw [hs]; linarith
  have hnN : N + J = 3*(K^2 + s)/2 := by linarith
  rw [hx]
  have hs1 : -1/3 ≤ s := by rw [hs]; linarith
  have hs2 : s ≤ 5*K := by rw [hs]; linarith
  have hxpos : 0 ≤ K^2 + s := by linarith
  set y := Real.sqrt (K^2 + s) with hy
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y^2 = K^2 + s := Real.sq_sqrt hxpos
  -- `y = √x` is close to `K`
  have hyu : y ≤ K + 3 := (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
  have hyl' : K - 1 ≤ y := (Real.le_sqrt (by linarith) hxpos).2 (by nlinarith)
  -- `K^2 ≤ n ≤ 9 K^2`
  have hn1 : K^2 ≤ N + J := by rw [hnN]; linarith
  have hn2 : N + J ≤ 9*K^2 := by rw [hnN]; linarith
  -- `x^{3/2} = y^3` is within `290 K` of `P = K^3 + (3/2) K s`
  set P := K^3 + 3/2*K*s with hP
  obtain ⟨hy3, hD⟩ := sqrt_cube_bound K s hK hs1 hs2
  obtain ⟨hD1, hD2⟩ := abs_le.mp hD
  -- logarithms: `L = log₂ n` is within `O(1)` of `2 C`
  set L := Real.logb 2 (N + J) with hL
  obtain ⟨hL1, hL2⟩ := log_bounds K (N + J) hK hn1 hn2
  have hlK0 : 0 ≤ Real.logb 2 K := Real.logb_nonneg (by norm_num) hK
  have hL0 : 0 ≤ L := by linarith
  have hLK : L ≤ 2*K + 4 := by linarith
  have hCL1 : -2 ≤ C - L/2 := by linarith
  have hCL2 : C - L/2 ≤ 1 := by linarith
  have hb1 : -2*K ≤ K*(C - L/2) := by
    have := mul_le_mul_of_nonneg_left hCL1 hK0; linarith
  have hb2 : K*(C - L/2) ≤ K := by
    have := mul_le_mul_of_nonneg_left hCL2 hK0; linarith
  have hb3 : -(3*K + 6) ≤ (K - y)*L/2 := by
    have := mul_nonneg (by linarith : 0 ≤ K - y + 3) hL0
    have : (K - y + 3)*L = (K - y)*L + 3*L := by ring
    linarith
  have hb4 : (K - y)*L/2 ≤ K + 2 := by
    have := mul_nonneg (by linarith : 0 ≤ 1 - (K - y)) hL0
    have : (1 - (K - y))*L = L - (K - y)*L := by ring
    linarith
  have hKC0 : 0 ≤ K*C := by positivity
  have hKC : K*C ≤ K^2 := by
    have := mul_le_mul_of_nonneg_left hCK hK0; nlinarith
  refine ⟨hn1, hn2, hy3, ?_, ?_⟩
  · have key : K^3 + R + J*K - (K^2+s)*y = R - 3/2*K^2 - K*C + 2*K - ((K^2+s)*y - P) := by
      rw [hP, hs]; ring
    rw [key, abs_le]; constructor <;> linarith
  · have key : K^3 + R + J*K - ((K^2+s)*y - (N+J) - y*L/2)
        = R + 2*K + 3/2*s - ((K^2+s)*y - P) - K*(C - L/2) - (K - y)*L/2 := by
      rw [hP, hnN, hs]; ring
    rw [key, abs_le]; constructor <;> linarith

/-- The common estimate behind `second_order_bound` and `ratio_bound`. Here `K` is the block
number of `n`, i.e. the integer cube root of `a n`. -/
private theorem core {n : ℕ} (hn : 0 < n) :
    ∃ K : ℝ, 1 ≤ K ∧ K^2 ≤ n ∧ (n : ℝ) ≤ 9*K^2 ∧
      K^3/2 ≤ (2*(n:ℝ)/3) * Real.sqrt (2*(n:ℝ)/3) ∧
      |(a n : ℝ) - (2*(n:ℝ)/3) * Real.sqrt (2*(n:ℝ)/3)| ≤ 296*K^2 ∧
      |(a n : ℝ) - ((2*(n:ℝ)/3) * Real.sqrt (2*(n:ℝ)/3) - n
          - Real.sqrt (2*(n:ℝ)/3) * Real.logb 2 n / 2)| ≤ 312*K := by
  obtain ⟨k, j, hk, hj, rfl⟩ := decompose hn
  have hA := block_value hk j hj.le
  have hE := entry_formula hk
  have hR := offset_lt hk
  have hW := width_le k
  have hc1 := Nat.le_pow_clog (by decide : 1 < 2) k
  have hc2 : 2 ^ Nat.clog 2 k < 2 * k := by
    have := hR; unfold offset at this; omega
  have hcK : Nat.clog 2 k ≤ k :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hK : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hKpos : (0:ℝ) < k := by linarith
  have hc1' : (k:ℝ) ≤ (2:ℝ)^(Nat.clog 2 k) := by exact_mod_cast hc1
  have hc2' : (2:ℝ)^(Nat.clog 2 k) < 2*k := by exact_mod_cast hc2
  have hpow : Real.logb 2 ((2:ℝ)^(Nat.clog 2 k)) = (Nat.clog 2 k : ℝ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
  have hl1 : Real.logb 2 k ≤ (Nat.clog 2 k : ℝ) :=
    hpow ▸ Real.logb_le_logb_of_le (by norm_num) hKpos hc1'
  have hl2 : (Nat.clog 2 k : ℝ) < Real.logb 2 k + 1 := by
    calc (Nat.clog 2 k : ℝ) = Real.logb 2 ((2:ℝ)^(Nat.clog 2 k)) := hpow.symm
      _ < Real.logb 2 (2*k) := Real.logb_lt_logb (by norm_num) (by positivity) hc2'
      _ = Real.logb 2 k + 1 := by
          rw [Real.logb_mul (by norm_num) hKpos.ne', Real.logb_self_eq_one (by norm_num)]; ring
  obtain ⟨h1, h2, h3, h4, h5⟩ := real_core (k:ℝ) (Nat.clog 2 k : ℝ) (j:ℝ) (offset k : ℝ)
    (entry k : ℝ) hK (by positivity) (by exact_mod_cast hR) (by positivity)
    (by exact_mod_cast (show j + 1 ≤ 3*k + 4 by omega)) (by positivity)
    (by exact_mod_cast hcK) (by exact_mod_cast hE) hl1 hl2
  have hA' : (a (entry k + j) : ℝ) = (k:ℝ)^3 + offset k + j*k := by rw [hA]; push_cast; ring
  have hn' : ((entry k + j : ℕ) : ℝ) = (entry k : ℝ) + j := by push_cast; ring
  rw [hA', hn']
  exact ⟨k, hK, h1, h2, h3, h4, h5⟩

/-- **Second-order asymptotics**, with an explicit constant: for every `n ≥ 1`,
`|a n - ((2n/3)^{3/2} - n - ½ √(2n/3) log₂ n)| ≤ 320 √n`. -/
theorem second_order_bound {n : ℕ} (hn : 0 < n) :
    |(a n : ℝ) - ((2*(n:ℝ)/3) * Real.sqrt (2*(n:ℝ)/3) - n
        - Real.sqrt (2*(n:ℝ)/3) * Real.logb 2 n / 2)| ≤ 320 * Real.sqrt n := by
  obtain ⟨K, hK, hn1, -, -, -, h⟩ := core hn
  have hKn : K ≤ Real.sqrt n := (Real.le_sqrt (by linarith) (by positivity)).2 hn1
  nlinarith

/-- **Rate of convergence** in Grau Ribas's conjecture, with an explicit constant: for every
`n ≥ 1`, `|a n / (2n/3)^{3/2} - 1| ≤ 1800 / √n`. -/
theorem ratio_bound {n : ℕ} (hn : 0 < n) :
    |(a n : ℝ) / ((2*(n:ℝ)/3) * Real.sqrt (2*(n:ℝ)/3)) - 1| ≤ 1800 / Real.sqrt n := by
  obtain ⟨K, hK, -, hn2, hden, h, -⟩ := core hn
  set D := (2*(n:ℝ)/3) * Real.sqrt (2*(n:ℝ)/3)
  have hKpos : 0 < K := by linarith
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hden
  have hsq : Real.sqrt n ≤ 3*K :=
    (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
  have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [show (a n : ℝ) / D - 1 = ((a n : ℝ) - D) / D by field_simp, abs_div, abs_of_pos hDpos,
    div_le_div_iff₀ hDpos hsqpos]
  -- `|a n - D| * √n ≤ 296 K^2 * 3K = 1776 * (K^3/2) ≤ 1800 * D`
  have h1 : |(a n : ℝ) - D| * Real.sqrt n ≤ 296*K^2 * (3*K) :=
    mul_le_mul h hsq hsqpos.le (by positivity)
  nlinarith

end GrauRibas
