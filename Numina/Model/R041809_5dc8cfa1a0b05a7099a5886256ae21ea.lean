import Mathlib

theorem algebra_70092 {x y : ℝ} (h : (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2)) = 1) : x + y = 0 := by
  have h1 : x + Real.sqrt (1 + x ^ 2) ≠ 0 := by
    by_contra h1a
    have h1a' : (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2)) = 0 := by
      rw [show x + Real.sqrt (1 + x ^ 2) = 0 by linarith [h1a]]
      norm_num
    linarith [h, h1a']
  have h2 : y + Real.sqrt (1 + y ^ 2) ≠ 0 := by
    by_contra h1b
    have h1b' : (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y^2)) = 0 := by
      rw [show y + Real.sqrt (1 + y ^ 2) = 0 by linarith [h1b]]
      norm_num
    linarith [h, h1b']
  have eq1 : (Real.sqrt (1 + x ^ 2) - x) * (Real.sqrt (1 + y ^ 2) - y) = 1 := by
    have eq2 : (x + Real.sqrt (1 + x ^ 2)) * (Real.sqrt (1 + x ^ 2) - x) = 1 := by 
      nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + x ^ 2 by nlinarith)]
    have eq3 : (y + Real.sqrt (1 + y ^ 2)) * (Real.sqrt (1 + y ^ 2) - y) = 1 := by 
      nlinarith [Real.sqrt_nonneg (1 + y ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + y ^ 2 by nlinarith)]
    have eq4 : (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2)) = 1 := h
    have eq5 : (Real.sqrt (1 + x ^ 2) - x) * (Real.sqrt (1 + y ^ 2) - y) = 1 := by
      have eq6 : ((x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2))) * ((x + Real.sqrt (1 + x ^ 2)) * (Real.sqrt (1 + x ^ 2) - x)) * ((y + Real.sqrt (1 + y ^ 2)) * (Real.sqrt (1 + y ^ 2) - y)) = 1 := by
        rw [show (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2)) = 1 by linarith [h], 
            show (x + Real.sqrt (1 + x ^ 2)) * (Real.sqrt (1 + x ^ 2) - x) = 1 by nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + x ^ 2 by nlinarith)],
            show (y + Real.sqrt (1 + y ^ 2)) * (Real.sqrt (1 + y ^ 2) - y) = 1 by nlinarith [Real.sqrt_nonneg (1 + y ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + y ^ 2 by nlinarith)]
            ]
        all_goals norm_num
      nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sqrt_nonneg (1 + y ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + x ^ 2 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + y ^ 2 by nlinarith)]
    exact_mod_cast eq5
  have h5 : x + y = 0 := by
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sqrt_nonneg (1 + y ^ 2), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 + x ^ 2 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 + y ^ 2 by nlinarith), 
      sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2), sq_nonneg (Real.sqrt (1 + x^2) - Real.sqrt (1 + y^2)
      )
    ]
  exact_mod_cast h5