import Mathlib
open Real

theorem algebra_1541 : sqrt (7 - sqrt 15 - sqrt (16 - 2*sqrt 15)) = sqrt 5 - sqrt 3 := by
  have h1 : sqrt (16 - 2 * sqrt 15) = sqrt 15 - 1 := by
    have h2 : (sqrt 15 - 1) ^ 2 = (16 - 2 * sqrt 15 : ℝ) := by
      have h3 : (sqrt 15 : ℝ) ^ 2 = 15 := by
        exact sq_sqrt (by norm_num)
      nlinarith [h3, Real.sqrt_nonneg 15, Real.sqrt_nonneg 15]
    have h4 : (sqrt 15 - 1 : ℝ) ≥ 0 := by
      have h5 : sqrt 15 ≥ 1 := by
        have h6 : sqrt 15 ≥ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
        have h7 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
        have h8 : sqrt 15 ≥ 1 := by linarith [h6, h7]
        linarith
      linarith [h5]
    rw [← h2]
    rw [Real.sqrt_sq h4]
  have h2 : 7 - sqrt 15 - sqrt (16 - 2 * sqrt 15) = (8 - 2 * sqrt 15 : ℝ) := by
    rw [h1]
    nlinarith [Real.sqrt_nonneg 15]
  rw [h2]
  have h3 : (sqrt 5 - sqrt 3 : ℝ) ^ 2 = (8 - 2 * sqrt 15 : ℝ) := by
    have h4 : (sqrt 5 : ℝ) ^ 2 = 5 := by
      exact sq_sqrt (by norm_num)
    have h5 : (sqrt 3 : ℝ) ^ 2 = 3 := by
      exact sq_sqrt (by norm_num)
    have h6 : sqrt 15 = sqrt 5 * sqrt 3 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    nlinarith [h4, h5, h6, Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sqrt_nonneg 15]
  have h7 : (sqrt 5 - sqrt 3 : ℝ) ≥ 0 := by
    have h8 : sqrt 5 ≥ sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
    have h9 : sqrt 5 - sqrt 3 ≥ 0 := by linarith [h8]
    linarith [h9]
  rw [← h3]
  rw [Real.sqrt_sq h7]