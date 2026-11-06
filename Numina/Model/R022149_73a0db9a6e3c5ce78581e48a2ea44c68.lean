import Mathlib

theorem algebra_21083 (x : ℝ) (hx : x > 0) (h : x = 2 * Real.sqrt 3 / Real.sqrt 2) :
    x = Real.sqrt 6 := by
  have h1 : x = 2 * Real.sqrt 3 / Real.sqrt 2 := h
  have h2 : x = Real.sqrt 6 := by
    rw [h1]
    have h4 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    have h5 : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num [Real.sq_sqrt]
    have h6 : 2 * Real.sqrt 3 / Real.sqrt 2 = Real.sqrt 3 * Real.sqrt 2 := by
      field_simp [show Real.sqrt 2 ≠ 0 by positivity, h4]
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h5]
    linarith [h6]
  exact h2