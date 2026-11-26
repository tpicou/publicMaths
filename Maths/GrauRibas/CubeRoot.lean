import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The cube-root recurrence A113768, indexed from 1. -/
namespace Maths.GrauRibas

/-- The auxiliary value at zero is outside the OEIS sequence. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => a (n + 1) + Nat.nthRoot 3 (a (n + 1))

private theorem step {n : ℕ} (hn : 0 < n) :
    a (n+1) = a n + Nat.nthRoot 3 (a n) := by
  cases n <;> first | rfl | omega

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

end Maths.GrauRibas
