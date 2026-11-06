import Mathlib

theorem algebra_188109 : √(6 + √27) - √(6 - √27) = √6 := by
  have h1 : √27 = 3 * √3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : (6 + √27 : ℝ) = 6 + 3 * √3 := by
    rw [h1]
    all_goals nlinarith
  have h3 : (6 - √27 : ℝ) = 6 - 3 * √3 := by
    rw [h1]
    all_goals nlinarith
  rw [h2, h3]
  have h4 : Real.sqrt (6 + 3 * Real.sqrt 3) ^ 2 = 6 + 3 * Real.sqrt 3 := Real.sq_sqrt (by positivity)
  have h5 : Real.sqrt (6 - 3 * Real.sqrt 3) ^ 2 = 6 - 3 * Real.sqrt 3 := by
    apply Real.sq_sqrt
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h6 : Real.sqrt (6 + 3 * Real.sqrt 3) * Real.sqrt (6 - 3 * Real.sqrt 3) = 3 := by
    have h7 : Real.sqrt (6 + 3 * Real.sqrt 3) * Real.sqrt (6 - 3 * Real.sqrt 3) = Real.sqrt ((6 + 3 * Real.sqrt 3) * (6 - 3 * Real.sqrt 3)) := by 
      rw [← Real.sqrt_mul (by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      )]
    rw [h7]
    have h8 : (6 + 3 * Real.sqrt 3) * (6 - 3 * Real.sqrt 3) = (9 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [h8]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h8 : (Real.sqrt (6 + 3 * Real.sqrt 3) - Real.sqrt (6 - 3 * Real.sqrt 3)) ^ 2 = 6 := by
    nlinarith [h4, h5, h6, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h9 : Real.sqrt (6 + 3 * Real.sqrt 3) - Real.sqrt (6 - 3 * Real.sqrt 3) ≥ 0 := by
    have h10 : Real.sqrt (6 + 3 * Real.sqrt 3) ≥ Real.sqrt (6 - 3 * Real.sqrt 3) := by
      apply Real.sqrt_le_sqrt
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h11 : Real.sqrt (6 - 3 * Real.sqrt 3) ≥ 0 := by 
      apply Real.sqrt_nonneg
    nlinarith
  have h17 : Real.sqrt (6 + 3 * Real.sqrt 3) - Real.sqrt (6 - 3 * Real.sqrt 3) = Real.sqrt (6 : ℝ) := by
    have h18 : Real.sqrt (6 + 3 * Real.sqrt 3) - Real.sqrt (6 - 3 * Real.sqrt 3) ≥ 0 := h9
    have h19 : Real.sqrt 6 ≥ 0 := by positivity
    have h20 : (Real.sqrt (6 + 3 * Real.sqrt 3) - Real.sqrt (6 - 3 * Real.sqrt 3)) ^ 2 = (Real.sqrt 6) ^ 2 := by
      rw [h8]
      all_goals
        norm_num
    nlinarith [h18, h19, h20]
  exact h17