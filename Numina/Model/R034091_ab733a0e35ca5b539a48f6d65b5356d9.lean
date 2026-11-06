import Mathlib

open Real

theorem algebra_243923 : sqrt (5 - 2 * sqrt 6) + sqrt (7 - 4 * sqrt 3) = 2 - sqrt 2 := by
  have h1 : sqrt (5 - 2 * sqrt 6) = Real.sqrt 3 - Real.sqrt 2 := by
    have h2 : (Real.sqrt 3 - Real.sqrt 2) ^ 2 = 5 - 2 * Real.sqrt 6 := by
      have h3 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ),
        Real.sqrt_nonneg (6 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
        Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
        h3, Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h4 : Real.sqrt 3 - Real.sqrt 2 ≥ 0 := by
      have h31 : Real.sqrt 2 < Real.sqrt 3 := by
        apply Real.sqrt_lt_sqrt
        all_goals linarith
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
    rw [←h2]
    field_simp [Real.sqrt_sq, h4]
    all_goals nlinarith

  have h5 : sqrt (7 - 4 * Real.sqrt 3) = (2 - Real.sqrt 3) := by
    have h6 : (2 - Real.sqrt 3) ^ 2 = 7 - 4 * Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ)]
    have h7 : 2 - Real.sqrt 3 ≥ 0 := by
      have h21 : Real.sqrt 3 ≤ (2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith
    rw [←h6]
    field_simp [Real.sqrt_sq, h7]
    all_goals nlinarith

  rw [h1, h5]
  nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (3 : ℝ)]