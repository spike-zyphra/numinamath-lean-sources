import Mathlib

open Real

theorem algebra_125616 {m n : ℝ} (hm : 1 < m) (hn : 1 < n) (hmn : m > n) :
    ((log (m * n)) ^ ((1 : ℝ) / 2) - (log m) ^ ((1 : ℝ) / 2)) <
    ((log m) ^ ((1 : ℝ) / 2) - (log (m / n)) ^ ((1 : ℝ) / 2)) := by 
  have h1 : 0 < m := by linarith
  have h2 : 0 < n := by linarith
  have h3 : 0 < m * n := by positivity
  have h4 : 0 < m / n := by
    apply div_pos
    linarith
    linarith
  have h5 : log (m * n) = log m + log n := by
    rw [log_mul (by linarith) (by linarith)]
  have h6 : log (m / n) = log m - log n := by
    rw [log_div (by linarith) (by linarith)]
  have h7 : log m > 0 := by
    apply log_pos
    linarith
  have h8 : log n > 0 := by
    apply log_pos
    linarith
  have h10 : log m > log n := by
    apply Real.log_lt_log
    all_goals linarith
  have h9 : log m - log n > 0 := by linarith
  suffices ((log (m * n)) ^ ((1 : ℝ) / 2) + (log (m / n)) ^ ((1 : ℝ) / 2)) < (2 * (log m) ^ ((1 : ℝ) / 2)) by 
    linarith 
  have h11 : (log (m * n)) ^ ((1 : ℝ) / 2) = Real.sqrt (log (m * n)) := by
    rw [Real.sqrt_eq_rpow]
  have h13 : (log (m / n)) ^ ((1 : ℝ) / 2) = Real.sqrt (log (m / n)) := by
    rw [Real.sqrt_eq_rpow]
  have h16 : (log m) ^ ((1 : ℝ) / 2) = Real.sqrt (log m) := by
    rw [Real.sqrt_eq_rpow]
  rw [h11, h13, h16]
  have h17 : Real.sqrt (log (m * n)) = Real.sqrt (log m + log n) := by
    rw [h5]
  have h18 : Real.sqrt (log (m / n)) = Real.sqrt (log m - log n) := by 
    rw [h6]
  rw [h17, h18]
  have h19 : Real.sqrt (log m + log n) + Real.sqrt (log m - log n) < 2 * Real.sqrt (log m) := by
    have h20 : Real.sqrt (log m + log n) ≥ 0 := by positivity
    have h21 : Real.sqrt (log m - log n) ≥ 0 := by positivity
    have h22 : Real.sqrt (log m) ≥ 0 := by positivity
    suffices (Real.sqrt (log m + log n) + Real.sqrt (log m - log n)) ^ 2 < (2 * Real.sqrt (log m)) ^ 2 by
      nlinarith
    have h23 : (Real.sqrt (log m + log n) + Real.sqrt (log m - log n)) ^ 2 = (Real.sqrt (log m + log n)) ^ 2 + (Real.sqrt (log m - log n)) ^ 2 + 2 * (Real.sqrt (log m + log n) * Real.sqrt (log m - log n)) := by ring
    have h24 : (2 * Real.sqrt (log m)) ^ 2 = 4 * (Real.sqrt (log m)) ^ 2 := by 
      ring_nf
    rw [h23]
    have h25 : (Real.sqrt (log m + log n)) ^ 2 = log m + log n := by
      rw [Real.sq_sqrt]
      nlinarith
    have h26 : (Real.sqrt (log m - log n)) ^ 2 = log m - log n := by
      rw [Real.sq_sqrt]
      nlinarith
    have h27 : Real.sqrt (log m + log n) * Real.sqrt (log m - log n) = Real.sqrt ((log m + log n) * (log m - log n)) := by
      rw [← Real.sqrt_mul (by positivity)]
    have h28 : (log m + log n) * (log m - log n) = (log m)^2 - (log n)^2 := by 
      ring
    have h29 : Real.sqrt ((log m + log n) * (log m - log n)) = Real.sqrt ((log m)^2 - (log n)^2) := by 
      rw [h28]
    have h30 : (Real.sqrt (log m + log n)) ^ 2 + (Real.sqrt (log m - log n)) ^ 2 + 2 * (Real.sqrt (log m + log n) * Real.sqrt (log m - log n)) = 2 * log m + 2 * Real.sqrt ((log m)^2 - (log n)^2) := by
      rw [h25, h26, h27, h29]
      ring_nf
    have h31 : 2 * log m + 2 * Real.sqrt ((log m)^2 - (log n)^2) < 4 * (Real.sqrt (log m)) ^ 2 := by
      have h32 : (Real.sqrt (log m)) ^ 2 = log m := by
        rw [Real.sq_sqrt]
        nlinarith
      have h34 : Real.sqrt ((log m)^2 - (log n)^2) < Real.sqrt ((log m)^2) := by
        apply Real.sqrt_lt_sqrt
        all_goals nlinarith [sq_pos_of_pos (show 0 < log n by linarith), sq_pos_of_pos (show 0 < log m by linarith)]
      have h35 : Real.sqrt ((log m)^2) = log m := by
        rw [Real.sqrt_sq (by positivity)]
      nlinarith [h32, h34, h35, Real.sqrt_nonneg ((log m)^2 - (log n)^2), Real.sqrt_nonneg ((log m)^2), sq_nonneg (log m - log n), sq_nonneg (log n), sq_pos_of_pos (show 0 < log n by linarith), sq_pos_of_pos (show 0 < log m by linarith)]
    linarith [h24, h30, h31]
  linarith [h19]