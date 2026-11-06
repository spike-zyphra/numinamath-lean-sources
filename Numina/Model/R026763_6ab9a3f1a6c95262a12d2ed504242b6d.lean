import Mathlib

open Real

theorem algebra_1713 : (sqrt 3 + sqrt 5) / (3 - sqrt 6 - sqrt 10 + sqrt 15) = sqrt 3 + sqrt 2 := by
  have h1 : sqrt 6 = sqrt 2 * sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : sqrt 10 = sqrt 2 * sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h3 : sqrt 15 = sqrt 3 * sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h_eq : 3 - sqrt 6 - sqrt 10 + sqrt 15 = (sqrt 3 - sqrt 2) * (sqrt 3 + sqrt 5) := by
    rw [show sqrt 6 = sqrt 2 * sqrt 3 by linarith [h1]]
    rw [show sqrt 10 = sqrt 2 * sqrt 5 by linarith [h2]]
    rw [show sqrt 15 = sqrt 3 * sqrt 5 by linarith [h3]]
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (5 : ℝ),
      Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
      Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num),
      Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num),
      sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 3 - sqrt 5), sq_nonneg (sqrt 2 * sqrt 3 * sqrt 5)
    ]
  have h4 : sqrt 3 > sqrt 2 := by
    apply Real.sqrt_lt_sqrt
    all_goals norm_num
  have h5 : sqrt 3 - sqrt 2 ≠ 0 := by
    linarith [h4]
  have h6 : sqrt 3 + sqrt 5 ≠ 0 := by
    positivity
  have h7 : (sqrt 3 - sqrt 2) * (sqrt 3 + sqrt 5) ≠ 0 := by
    apply mul_ne_zero
    exact h5
    exact h6
  have h_eq2 : (sqrt 3 + sqrt 5) / (3 - sqrt 6 - sqrt 10 + sqrt 15) = (sqrt 3 + sqrt 5) / ((sqrt 3 - sqrt 2) * (sqrt 3 + sqrt 5)) := by
    rw [h_eq]
    all_goals try norm_num
  have h8 : (sqrt 3 + sqrt 5) / ((sqrt 3 - sqrt 2) * (sqrt 3 + sqrt 5)) = 1 / (sqrt 3 - sqrt 2) := by
    have h9 : (sqrt 3 + sqrt 5) ≠ 0 := by positivity
    have h10 : (sqrt 3 - sqrt 2) ≠ 0 := h5
    have h11 : (sqrt 3 - sqrt 2) * (sqrt 3 + sqrt 5) ≠ 0 := h7
    field_simp [(show (sqrt 3 + sqrt 5) ≠ 0 by exact h9), h10, h11]
    <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h9 : (1 / (sqrt 3 - sqrt 2) ) = sqrt 3 + sqrt 2 := by
    have h10 : sqrt 3 - sqrt 2 ≠ 0 := h5
    field_simp [(show (sqrt 3 - sqrt 2 : ℝ) ≠ 0 by exact h10)]
    <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  rw [h_eq2, h8, h9]
  all_goals try ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring