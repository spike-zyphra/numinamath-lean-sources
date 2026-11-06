import Mathlib

theorem algebra_7656 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : Real.sqrt (2 * x) + Real.sqrt y = 13) (h2 : Real.sqrt (8 * x) + Real.sqrt (9 * y) = 35) :
    20 * x + 23 * y = 2023 := by
  have h3 : Real.sqrt (8 * x) = 2 * Real.sqrt (2 * x) := by
    have h4 : Real.sqrt (8 * x) = Real.sqrt (4 * (2 * x)) := by ring_nf
    rw [h4]
    have h5 : Real.sqrt (4 * (2 * x)) = Real.sqrt (4 : ℝ) * Real.sqrt (2 * x) := by
      rw [Real.sqrt_mul (by positivity)]
    rw [h5]
    have h6 : Real.sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h6]
  have h7 : Real.sqrt (9 * y) = 3 * Real.sqrt y := by
    have h8 : Real.sqrt (9 * y) = Real.sqrt (9 * (y : ℝ)) := by ring_nf
    rw [h8]
    have h9 : Real.sqrt (9 * (y : ℝ)) = Real.sqrt (9 : ℝ) * Real.sqrt (y : ℝ) := by
      rw [Real.sqrt_mul (by positivity)]
    rw [h9]
    have h10 : Real.sqrt (9 : ℝ) = 3 := by
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h10]
  rw [h3, h7] at h2
  have eq1 : Real.sqrt (2 * x) + Real.sqrt y = 13 := by linarith
  have eq2 : 2 * Real.sqrt (2 * x) + 3 * Real.sqrt y = 35 := by linarith
  have h9 : Real.sqrt (2 * x) = 4 := by
    linarith [eq1, eq2]
  have h8 : Real.sqrt y = 9 := by
    linarith [eq1, eq2]
  have hx2 : x = 8 := by 
    have h14 : Real.sqrt (2 * x) = 4 := h9
    have : 2 * x = 16 := by
      calc
        2 * x = (Real.sqrt (2 * x)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 4 ^ 2 := by rw [h14]
        _ = 16 := by norm_num
    linarith
  have hy2 : y = 81 := by
    have h15 : Real.sqrt y = 9 := h8
    have : y = 81 := by
      calc
        y = (Real.sqrt y) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 9 ^ 2 := by rw [h15]
        _ = 81 := by norm_num
    linarith
  rw [hx2, hy2]
  norm_num