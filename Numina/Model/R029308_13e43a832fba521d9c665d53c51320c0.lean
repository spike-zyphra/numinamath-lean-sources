import Mathlib

open Real

theorem inequalities_36212 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) * (a + c) ≥ 2 * sqrt (a * b * c * (a + b + c)) := by
  have h1 : 0 < a * b * c * (a + b + c) := by
    positivity
  have h2 : sqrt (a * b * c * (a + b + c)) ≥ 0 := by positivity
  have h3 : ((a + b) * (a + c)) ^ 2 ≥ 4 * (a * b * c * (a + b + c)) := by
    nlinarith [sq_nonneg (a * (a + b + c) - b * c), sq_nonneg (a ^ 2 - b * c), sq_nonneg (a * (b - c)), sq_nonneg ((a + b) - (a + c)), sq_nonneg (b - c), sq_nonneg (a + b - a - c), sq_nonneg (a ^ 2), sq_nonneg (b * c), sq_nonneg (a * (b + c)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos ha (show 0 < a + b + c by positivity)]
  have h4 : (2 * sqrt (a * b * c * (a + b + c))) ^ 2 = 4 * (a * b * c * (a + b + c)) := by
    calc
      (2 * sqrt (a * b * c * (a + b + c))) ^ 2 = 4 * (sqrt (a * b * c * (a + b + c)) ^ 2) := by ring
      _ = 4 * (a * b * c * (a + b + c)) := by
        rw [Real.sq_sqrt]
        positivity
  have h5 : ((a + b) * (a + c : ℝ)) ≥ 0 := by positivity
  have h6 : 2 * sqrt (a * b * c * (a + b + c)) ≥ 0 := by positivity
  nlinarith [Real.sqrt_nonneg (a * b * c * (a + b + c)), h3, h4, sq_nonneg (( (a + b) * (a + c) ) - 2 * sqrt (a * b * c * (a + b + c))), sq_nonneg (sqrt (a * b * c * (a + b + c))), h1]