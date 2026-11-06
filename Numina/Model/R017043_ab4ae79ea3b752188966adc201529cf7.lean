import Mathlib

theorem algebra_195667 (x : ℝ) (hx : x = √2 + √3) :
    x^4 - 10 * x^2 + 1 = 0 := by
  rw [hx]
  have h1 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3 : (√2 : ℝ) * (√3 : ℝ) = √6 := by
    have h4 : (√2 : ℝ) * (√3 : ℝ) = √(2 * 3 : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
      all_goals norm_num
    rw [h4]
    all_goals norm_num [Real.sqrt_mul]
    all_goals norm_num
  have h4 : (√2 + √3 : ℝ) ^ 2 = 5 + 2 * √6 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), 
      Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num : (2 : ℝ) ≥ 0), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num : (3 : ℝ) ≥ 0), 
      h1, h2, h3, Real.sqrt_nonneg 6
    ]
  have h5 : (√2 + √3 : ℝ) ^ 4 = (5 + 2 * √6) ^ 2 := by
    calc
      (√2 + √3 : ℝ) ^ 4
          = ((√2 + √3 : ℝ) ^ 2) ^ 2 := by ring
      _   = (5 + 2 * √6) ^ 2 := by rw [h4]
  have h6 : (5 + 2 * √6 : ℝ) ^ 2 = 49 + 20 * √6 := by
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num : (6 : ℝ) ≥ 0)]
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, h1, h2, h4, h5, h6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num : (6 : ℝ) ≥ 0)]