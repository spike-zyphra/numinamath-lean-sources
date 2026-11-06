import Mathlib

theorem algebra_314548 (a b c : ℝ) (ha : a ≠ 0) (hA : a * Real.sqrt 3 + b = Real.sqrt 3 + 2)
    (hB : a * (-1) + b = Real.sqrt 3) (hC : a * c + b = 2 - c) :
    a^2 + b^2 + c^2 - a * b - b * c - c * a = 4 + Real.sqrt 3 := by
  have eq1 : b = Real.sqrt 3 + a := by
    linarith 
  have eq2 : a * Real.sqrt 3 + (Real.sqrt 3 + a) = Real.sqrt 3 + 2 := by 
    rw [eq1] at hA 
    linarith
  have eq3 : a = Real.sqrt 3 - 1 := by 
    have h1 : a * (Real.sqrt 3 + 1) = 2 := by 
      have h2 : a * Real.sqrt 3 + a = 2 := by 
        nlinarith 
      linarith 
    have h4 : (Real.sqrt 3 - 1) * (Real.sqrt 3 + 1) = 2 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h5 : a = Real.sqrt 3 - 1 := by 
      have h3 : a * (Real.sqrt 3 + 1) = (Real.sqrt 3 - 1) * (Real.sqrt 3 + 1) := by 
        linarith [h1, h4] 
      have h6 : a = Real.sqrt 3 - 1 := by 
        apply (mul_left_inj' (show (Real.sqrt 3 + 1 : ℝ) ≠ 0 by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        )).mp 
        linarith 
      linarith 
    linarith 
  have eq4 : b = 2 * Real.sqrt 3 - 1 := by 
    rw [eq3] at eq1 
    linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  have eq5 : (Real.sqrt 3 - 1) * c + (2 * Real.sqrt 3 - 1) = (2 - c) := by
    rw [eq3, eq4] at hC
    linarith 
  have eq6 : c = Real.sqrt 3 - 2 := by 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  rw [eq3, eq4, eq6]
  nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]