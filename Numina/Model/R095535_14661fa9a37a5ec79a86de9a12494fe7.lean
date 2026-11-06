import Mathlib

theorem algebra_202984 (α : ℝ) (h : 0 < α) (h' : 6 * Real.sqrt 3 / (3 * Real.sqrt 2 + 2 * Real.sqrt 3) = 3 * Real.sqrt α - 6) :
    α = 6 := by
  have h1 : 6 * Real.sqrt 3 / (3 * Real.sqrt 2 + 2 * Real.sqrt 3) = 3 * Real.sqrt 6 - 6 := by
    have denom_ne_zero : 3 * Real.sqrt 2 + 2 * Real.sqrt 3 ≠ 0 := by
      have h1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
      have h2 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)
      have h3 : 0 < 3 * Real.sqrt 2 := by nlinarith
      have h4 : 0 < 2 * Real.sqrt 3 := by nlinarith
      linarith
    field_simp [denom_ne_zero]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
    have h4 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      calc
        Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
        _ = Real.sqrt 2 * Real.sqrt 3 := by rw [Real.sqrt_mul (show 0 ≤ (2 : ℝ) by norm_num)]
    rw [h4]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num),
      h2, h3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
  rw [h1] at h'
  have h3 : Real.sqrt α = Real.sqrt 6 := by
    linarith
  have h4 : α = 6 := by
    have h5 : (Real.sqrt α) ^ 2 = (Real.sqrt 6) ^ 2 := by rw [h3]
    rw [Real.sq_sqrt (show 0 ≤ α by linarith), Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num)] at h5
    linarith
  exact h4