import Mathlib

open Real

theorem inequalities_599372 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    sqrt (2) < sqrt (a + 1 / 2) + sqrt (b + 1 / 2) ∧
    sqrt (a + 1 / 2) + sqrt (b + 1 / 2) ≤ 2 := by

  have h1 : 0 < b := hb
  have h2 : a + b = 1 := h
  have h3 : sqrt (2) < sqrt (a + 1 / 2) + sqrt (b + 1 / 2) := by
    have h4 : (sqrt (2) : ℝ) ^ 2 < (sqrt (a + 1 / 2) + sqrt (b + 1 / 2)) ^ 2 := by
      have h5 : (sqrt (2) : ℝ) ^ 2 = (2 : ℝ) := by
        rw [Real.sq_sqrt]
        all_goals linarith
      have h6 : (sqrt (a + 1 / 2) + sqrt (b + 1 / 2)) ^ 2 =
          (sqrt (a + 1 / 2) )^2 + (sqrt (b + 1 / 2)) ^ 2 + 2 * (sqrt (a + 1 / 2) * sqrt (b + 1 / 2)) := by
        ring
      have h7 : (sqrt (a + 1 / 2) : ℝ) ^ 2 = a + 1 / 2 := by
        rw [Real.sq_sqrt]
        linarith
      have h8 : (sqrt (b + 1 / 2) : ℝ) ^ 2 = b + 1 / 2 := by
        rw [Real.sq_sqrt]
        linarith
      rw [h6, h7, h8]
      nlinarith [sq_nonneg (sqrt (a + 1 / 2) - sqrt (b + 1 / 2)), Real.sqrt_nonneg (2), Real.sqrt_nonneg (a + 1 / 2), Real.sqrt_nonneg (b + 1 / 2), h5, show sqrt (2) > 0 by positivity, mul_pos ha hb]
    have h8 : 0 < sqrt (2) := by positivity
    have h9 : 0 < sqrt (a + 1 / 2) + sqrt (b + 1 / 2) := by positivity
    nlinarith [Real.sqrt_nonneg (2), Real.sqrt_nonneg (a + 1 / 2), Real.sqrt_nonneg (b + 1 / 2), h4, show sqrt (2) > 0 by positivity, show sqrt (a + 1 / 2) + sqrt (b + 1 / 2) > 0 by positivity]
  have h4 : sqrt (a + 1 / 2) + sqrt (b + 1 / 2) ≤ 2 := by
    have h5 : (sqrt (a + 1 / 2) + sqrt (b + 1 / 2)) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      have h6 : (sqrt (a + 1 / 2) + sqrt (b + 1 / 2)) ^ 2 =
          (sqrt (a + 1 / 2) )^2 + (sqrt (b + 1 / 2)) ^ 2 + 2 * (sqrt (a + 1 / 2) * sqrt (b + 1 / 2)) := by
        ring
      have h7 : (sqrt (a + 1 / 2) : ℝ) ^ 2 = a + 1 / 2 := by
        rw [Real.sq_sqrt]
        linarith
      have h8 : (sqrt (b + 1 / 2) : ℝ) ^ 2 = b + 1 / 2 := by
        rw [Real.sq_sqrt]
        linarith
      rw [h6, h7, h8]
      nlinarith [sq_nonneg (sqrt (a + 1 / 2) - sqrt (b + 1 / 2)), sq_nonneg (a - b), Real.sqrt_nonneg (a + 1 / 2), Real.sqrt_nonneg (b + 1 / 2), Real.sq_sqrt (show 0 ≤ (a + 1 / 2 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b + 1 / 2 : ℝ) by linarith), h, mul_pos ha hb]
    have h9 : 0 ≤ (sqrt (a + 1 / 2) + sqrt (b + 1 / 2) : ℝ) := by positivity
    have h10 : 0 ≤ (2 : ℝ) := by linarith
    nlinarith [Real.sqrt_nonneg (a + 1 / 2), Real.sqrt_nonneg (b + 1 / 2), Real.sq_sqrt (show 0 ≤ (a + 1 / 2 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b + 1 / 2 : ℝ) by linarith), h5, sq_nonneg (sqrt (a + 1 / 2) + sqrt (b + 1 / 2) - 2)]
  constructor
  · exact h3
  · exact h4