import Mathlib

theorem algebra_148117 (m : ℝ) (hm : m < 0) (h : (1 / 2) * (1 / 5) * (2 * m ^ 2) = 242) :
    m = -11 * Real.sqrt 10 := by
  have h1 : m ^ 2 = 1210 := by
    linarith
  have h2 : m = - Real.sqrt 1210 := by
    have : m = - Real.sqrt (m ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_neg hm]
      ring
    rw [h1] at this
    exact this
  have h3 : Real.sqrt 1210 = 11 * Real.sqrt 10 := by
    calc
      Real.sqrt 1210 = Real.sqrt (11 ^ 2 * 10) := by norm_num
      _ = Real.sqrt (11 ^ 2) * Real.sqrt 10 := by rw [Real.sqrt_mul (by norm_num)]
      _ = 11 * Real.sqrt 10 := by rw [Real.sqrt_sq (by norm_num)]
  rw [h3] at h2
  linarith