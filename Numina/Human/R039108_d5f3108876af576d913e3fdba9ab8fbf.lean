import Mathlib

open Real

/- There is a unique positive real number x such that the three numbers log_8(2x), log_4(x), and log_2(x) in that order, form a geometric progression with positive common ratio. The number x can be written as m/n, where m and n are relatively prime positive integers. Find m + n. -/
theorem algebra_98102 (x : ℝ) (m n : ℕ) (hx : x > 0) (hm: m > 0) (hn: n > 0) (hmn_cop: Nat.Coprime m n) (hxmn : x = (m:ℝ) / n)
(hl₁: logb 8 (2 * x) ≠ 0) (hl₂: logb 4 x ≠ 0) (hl₃: logb 2 x ≠ 0)
(h : ∃ r > 0, logb 8 (2 * x) * r = logb 4 x ∧ logb 4 x * r = logb 2 x) : m + n = 17 := by
  -- define bunch of facts related to numbers that will be used in proof
  have : 2 ≠ 0 := by norm_num
  have : log 2 ≠ 0 := by norm_num
  have : 0 < (1:ℝ)/16 := by norm_num
  have : log 8 = 3 * log 2 := by
    calc
      log 8 = log (2^3) := by norm_num
      _ = 3 * log 2 := by exact log_pow 2 3
  have : log 4 = 2 * log 2 := by
    calc
      log 4 = log (2^2) := by norm_num
      _ = 2 * log 2 := by exact log_pow 2 2
  have : x ≠ 0 := by linarith
  have : x ≠ 1 := by
    by_contra hx
    have : logb 2 x = 0 := by simp [hx]
    contradiction
  have : log x ≠ 0 := by exact log_ne_zero_of_pos_of_ne_one hx ‹x ≠ 1›
  -- extract r, r > 0, log_8(2x) * r = log_4(x) and log_4(x) * r = log_2(x)
  obtain ⟨r, hr, hr1, hr2⟩ := h
  -- by simplifying last equation get r = log 4 / log 2 = 2
  have hrv : r = (logb 2 x) / (logb 4 x) := by field_simp; linarith
  have hrv : r = log 4 / log 2 := by
    simp [logb] at hrv
    field_simp at hrv
    calc
      r = r * (log 2 * log x) / (log 2 * log x) := by field_simp
      _ = log x * log 4 / (log 2 * log x) := by rw [hrv]
      _ = log 4 * log x / log x / log 2 := by ring
      _ = log 4 / log 2 := by field_simp
  have hrv : r = logb 2 (2^2) := by norm_num; assumption
  have hrv : r = 2 := by simp [hrv, logb_pow]
  -- now plug in r into log_8(2x) * r = log_4(x) and simplify to get r = -4 * log 2
  rw [hrv] at hr1
  simp [logb] at hr1
  simp [log_mul, ‹x ≠ 0›, ‹2 ≠ 0›] at hr1
  rw [‹log 8 = 3 * log 2›, ‹log 4 = 2 * log 2›] at hr1
  ring_nf at hr1
  field_simp [‹log 2 ≠ 0›] at hr1
  have hlx : log x * log 2 = -4 * log 2 * log 2 := by linarith
  have hlx : log x  = (-4) * log 2 := by
    calc
      log x = log x * log 2 / log 2 := by field_simp
      _ = -4 * log 2 * log 2 / log 2 := by rw [hlx]
      _ = -4 * log 2 := by field_simp
  -- so x = 1/16 this means m = 1 and n = 16.
  have hlx: log x = log ((2:ℝ) ^ (-4:ℤ)) := by simp [hlx, log_pow]
  have hlx: log x = log ((1:ℝ)/16) := by
    norm_num at hlx
    assumption
  have hx' : x = (1:ℝ)/16 := by
    calc
      x = exp (log x) := by simp [exp_log, hx]
      _ = exp (log ((1:ℝ)/16)) := by rw [hlx]
      _ = (1:ℝ)/16 := by rw [exp_log ‹0 < (1:ℝ)/16›]
  rw [hxmn] at hx'
  field_simp at hx'
  norm_cast at hx'
  have : m ∣ n := by use 16; linarith
  have hm' : m = 1 := by exact Nat.Coprime.eq_one_of_dvd hmn_cop this
  rw [hm'] at hx'
  norm_num at hx'
  subst hx'
  subst hm'
  norm_num