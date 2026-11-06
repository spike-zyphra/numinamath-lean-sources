import Mathlib

theorem algebra_1000 (x : ℝ) (hx : x^3 = 5 * Real.sqrt 2 - 7) :
    x = Real.sqrt 2 - 1 := by
  have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
  have h2 : Real.sqrt 2 ^ 4 = 4 := by 
    calc 
      Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
      _ = 2 ^ 2 := by rw [h1]
      _ = 4 := by norm_num
  have h3 : (Real.sqrt 2 - 1 : ℝ) ^ 3 = 5 * Real.sqrt 2 - 7 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 ^ 2 - 2 : ℝ), sq_nonneg (Real.sqrt 2 - 1 : ℝ), h1, h2]
  have h4 : x ^ 3 = (Real.sqrt 2 - 1 : ℝ) ^ 3 := by
    rw [h3] at *
    linarith
  have h5 : x = (Real.sqrt 2 - 1 : ℝ) := by
    have h6 : x ^ 3 - ((Real.sqrt 2 - 1 : ℝ) : ℝ) ^ 3 = 0 := by nlinarith
    have h7 : (x - (Real.sqrt 2 - 1 : ℝ)) * (x ^ 2 + x * (Real.sqrt 2 - 1 : ℝ) + ( (Real.sqrt 2 - 1 : ℝ) : ℝ) ^ 2 ) = 0 := by
      ring_nf at h6 ⊢
      nlinarith
      -- factorize
   
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case where x - (sqrt 2 - 1) = 0
      linarith
    · -- Case where quadratic factor is zero
      have h10 : x ^ 2 + x * (Real.sqrt 2 - 1 : ℝ) + ( (Real.sqrt 2 - 1 : ℝ) : ℝ) ^ 2 = 0 := by 
        nlinarith
      nlinarith [sq_nonneg (x + (Real.sqrt 2 - 1) / 2 : ℝ), sq_nonneg (Real.sqrt 2 - (5 : ℝ) / 4 : ℝ),
          Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith), sq_nonneg (x ^ 2), sq_nonneg (Real.sqrt 2 ^ 2 - 2 : ℝ),
          sq_nonneg (x - Real.sqrt 2), sq_nonneg (x + Real.sqrt 2), h1, h2
      ]
  linarith [h5]