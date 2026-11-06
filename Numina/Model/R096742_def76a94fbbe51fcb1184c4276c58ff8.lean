import Mathlib

theorem algebra_20259 (x : ℝ) (hx : x ^ 3 = 5) : Real.logb x 125 = 9 := by
  have hx_pos : x > 0 := by
    by_contra h
    push_neg at h
    have h1 : x ≤ 0 := by linarith
    have h2 : x ^ 3 ≤ 0 := by nlinarith [sq_nonneg x, sq_nonneg (x + 1), sq_nonneg (x - 1)]
    linarith
  -- Let's now compute $\logb x 125$ where $x^3 = 5$.
  have hx2 : Real.log x = Real.log 5 / 3 := by
    have h2 : x ^ 3 = 5 := hx
    have h3 : Real.log (x ^ 3) = Real.log 5 := by
      rw [h2]
    have h4 : Real.log (x ^ 3) = 3 * Real.log x := by
      simp [Real.log_pow]
    have h5 : 3 * Real.log x = Real.log 5 := by linarith [h3, h4]
    linarith
  have h5 : Real.log 125 = 3 * Real.log 5 := by
    have h6 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [h6]
    simp [Real.log_pow]
  have h7 : Real.log 5 ≠ 0 := by
    have h8 : Real.log 5 > 0 := by
      apply Real.log_pos
      norm_num
    linarith
  rw [Real.logb]
  rw [hx2]
  field_simp [h5, h7]
  <;> nlinarith