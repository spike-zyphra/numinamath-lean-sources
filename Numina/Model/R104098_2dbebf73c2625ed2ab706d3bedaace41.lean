import Mathlib

theorem algebra_97485 {m : ℝ} (hm : m > 0) (h : (m - 1) * m = 3 - m) :
    m = Real.sqrt 3 := by
  have h1 : m^2 = 3 := by
    linarith
  
  have h3 : m ≥ 0 := by linarith
  
  have h4 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)

  have h5 : m^2 = (Real.sqrt 3) ^ 2 := by
    linarith [h1, h4]

  have h6 : m = Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, h3]

  exact h6