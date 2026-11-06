import Mathlib

theorem algebra_318478 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x^2 + y^2 = 24) (h2 : (Real.sqrt x + Real.sqrt y)^4 + (Real.sqrt x - Real.sqrt y)^4 = 180) :
    x * y = 11 := by

  have h3 : x^2 + y^2 + 6 * x * y = 90 := by

    have h2_expanded : (Real.sqrt x + Real.sqrt y) ^ 4 + (Real.sqrt x - Real.sqrt y) ^ 4 = 2 * (x^2 + 6 * x * y + y^2) := by

      have h : (Real.sqrt x + Real.sqrt y) ^ 4 = (Real.sqrt x) ^ 4 + 4 * (Real.sqrt x) ^ 3 * (Real.sqrt y) + 6 * (Real.sqrt x) ^ 2 * (Real.sqrt y) ^ 2 + 4 * (Real.sqrt x) * (Real.sqrt y) ^ 3 + (Real.sqrt y) ^ 4 := by
        ring
      have h' : (Real.sqrt x - Real.sqrt y) ^ 4 = (Real.sqrt x) ^ 4 - 4 * (Real.sqrt x) ^ 3 * (Real.sqrt y) + 6 * (Real.sqrt x) ^ 2 * (Real.sqrt y) ^ 2 - 4 * (Real.sqrt x) * (Real.sqrt y) ^ 3 + (Real.sqrt y) ^ 4 := by
        ring
      rw [h, h'] 

      have h_sqrt_sq_x : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
      have h_sqrt_sq_y : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (by linarith)


      rw [h_sqrt_sq_x, h_sqrt_sq_y]
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]

    rw [h2_expanded] at h2
    linarith only [h2]

  linarith only [h1, h3] 
