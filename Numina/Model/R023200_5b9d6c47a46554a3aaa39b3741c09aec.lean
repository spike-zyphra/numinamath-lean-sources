import Mathlib

theorem algebra_322496 {x y : ℝ} (h : x^2 + y^2 - 4 * x - 2 * y + 5 = 0) :
    (Real.sqrt x + y) / Real.sqrt (3 * y - 2 * Real.sqrt x) = 3 + 2 * Real.sqrt 2 := by
  have h1 : (x - 2)^2 + (y - 1)^2 = 0 := by
    nlinarith
  have hx_eq : x = 2 := by 
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1)]
  have hy_eq : y = 1 := by 
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1)]
  have h2 : Real.sqrt x = Real.sqrt 2 := by 
    rw [hx_eq]
  have h3 : (3 * y - 2 * Real.sqrt x) = (3 - 2 * Real.sqrt 2) := by
    rw [hy_eq, h2]
    all_goals linarith
  have h4 : Real.sqrt (3 * y - 2 * Real.sqrt x) = Real.sqrt 2 - 1 := by
    rw [h3]
    have h5 : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by
      have h6 : (Real.sqrt 2 - 1 : ℝ) ^ 2 = (3 - 2 * Real.sqrt 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h7 : Real.sqrt (3 - 2 * Real.sqrt 2 : ℝ) = Real.sqrt ((Real.sqrt 2 - 1 : ℝ) ^ 2) := by
        rw [h6]
      rw [h7]
      have h8 : Real.sqrt ((Real.sqrt 2 - 1 : ℝ) ^ 2) = Real.sqrt 2 - 1 := by
        rw [Real.sqrt_sq_eq_abs]
        have h9 : (Real.sqrt 2 - 1 : ℝ) ≥ 0 := by
          have h10 : 1 < (Real.sqrt 2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
          linarith
        rw [abs_of_nonneg h9]
      linarith
    linarith
  have h5 : Real.sqrt x + y = Real.sqrt 2 + 1 := by 
    rw [h2, hy_eq]
    all_goals linarith
  rw [h4, h5]
  have h6 : Real.sqrt 2 - 1 > 0 := by
    have h1 : 1 < Real.sqrt 2 := by
      rw [Real.lt_sqrt]
      all_goals norm_num
    linarith
  field_simp [show Real.sqrt 2 - 1 > 0 by linarith [h6]]
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]