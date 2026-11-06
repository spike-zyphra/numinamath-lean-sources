import Mathlib

open Real

theorem inequalities_66979 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) * (a + c) ≥ 2 * sqrt (a * b * c * (a + b + c)) := by
  have h : 0 < a * b * c * (a + b + c) := by
    positivity

  have h1 : ((a + b) * (a + c)) ^ 2 ≥ 4 * (a * b * c * (a + b + c)) := by
    nlinarith [sq_nonneg (a * (a + b + c) - b * c), sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b - c), sq_nonneg (a * (a + b - c)), sq_nonneg (a * (a + c - b)), sq_nonneg (a * (b - c)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)]
  have h2 : 0 ≤ (a + b) * (a + c) := by
    positivity
  have h3 : 0 ≤ (2 * sqrt (a * b * c * (a + b + c))) := by
    positivity
  have h4 : (2 * sqrt (a * b * c * (a + b + c))) ^ 2 = 4 * (a * b * c * (a + b + c)) := by
    calc
      (2 * sqrt (a * b * c * (a + b + c))) ^ 2 = 4 * (sqrt (a * b * c * (a + b + c)) ^ 2) := by
        ring_nf
      _ = 4 * (a * b * c * (a + b + c)) := by
        rw [Real.sq_sqrt]
        positivity
  have h5 : ((a + b) * (a + c)) ^ 2 ≥ (2 * sqrt (a * b * c * (a + b + c))) ^ 2 := by
    nlinarith [h1, h4, h2, Real.sqrt_nonneg (a * b * c * (a + b + c))]
  have h6 : (a + b) * (a + c) ≥ 2 * sqrt (a * b * c * (a + b + c)) := by
    nlinarith [h5, Real.sqrt_nonneg (a * b * c * (a + b + c)), show 0 ≤ (a + b) * (a + c) by positivity]
  exact h6