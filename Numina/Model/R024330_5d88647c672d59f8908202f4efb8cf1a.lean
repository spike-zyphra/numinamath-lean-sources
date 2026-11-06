import Mathlib

theorem inequalities_599162 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    2 ≤ Real.sqrt (2 * x ^ 2 + y) + Real.sqrt (x + 2 * y ^ 2) := by

  have hy' : y = 1 - x := by linarith
  rw [hy'] -- Substitute y with 1 - x
  have h1 : Real.sqrt (2 * x ^ 2 + (1 - x)) + Real.sqrt (x + 2 * (1 - x) ^ 2) ≥ (2 : ℝ) := by
    have h2 : (Real.sqrt (2 * x ^ 2 + (1 - x)) + Real.sqrt (x + 2 * (1 - x) ^ 2)) ^ 2 ≥ (4 : ℝ) := by
      have h3 : (Real.sqrt (2 * x ^ 2 + (1 - x)) ) ^ 2 = (2 * x ^ 2 + (1 - x) : ℝ) := by
        exact Real.sq_sqrt (by nlinarith)
      have h4 : (Real.sqrt (x + 2 * (1 - x) ^ 2) ) ^ 2 = (x + 2 * (1 - x) ^ 2 : ℝ) := by
        exact Real.sq_sqrt (by nlinarith)
      have h5 : (Real.sqrt (2 * x ^ 2 + (1 - x)) + Real.sqrt (x + 2 * (1 - x) ^ 2)) ^ 2 =
          (Real.sqrt (2 * x ^ 2 + (1 - x)) ) ^ 2 + (Real.sqrt (x + 2 * (1 - x) ^ 2) ) ^ 2 + 2 * (Real.sqrt (2 * x ^ 2 + (1 - x)) * Real.sqrt (x + 2 * (1 - x) ^ 2) ) := by ring
      rw [h5, h3, h4]
      nlinarith [Real.sqrt_nonneg (2 * x ^ 2 + (1 - x)), Real.sqrt_nonneg (x + 2 * (1 - x) ^ 2), 
        sq_nonneg (Real.sqrt (2 * x ^ 2 + (1 - x)) - Real.sqrt (x + 2 * (1 - x) ^ 2)), 
        sq_nonneg (x - (1 / 2)), 
        Real.sq_sqrt (show 0 ≤ (2 * x ^ 2 + (1 - x) : ℝ) by nlinarith), 
        Real.sq_sqrt (show 0 ≤ (x + 2 * (1 - x) ^ 2 : ℝ) by nlinarith), 
        mul_nonneg (Real.sqrt_nonneg (2 * x ^ 2 + (1 - x))) (Real.sqrt_nonneg (x + 2 * (1 - x) ^ 2))
      ]
    have h3 : Real.sqrt (2 * x ^ 2 + (1 - x)) + Real.sqrt (x + 2 * (1 - x) ^ 2) ≥ (2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2 * x ^ 2 + (1 - x)), Real.sqrt_nonneg (x + 2 * (1 - x) ^ 2), Real.sq_sqrt (show 0 ≤ (2 * x ^ 2 + (1 - x) : ℝ) by nlinarith), Real.sq_sqrt (show 0 ≤ (x + 2 * (1 - x) ^ 2 : ℝ) by nlinarith), h2]
    linarith
  linarith [h1]