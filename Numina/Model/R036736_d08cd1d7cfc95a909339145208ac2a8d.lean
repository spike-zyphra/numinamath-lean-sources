import Mathlib

theorem algebra_101267 {x : ℝ} (hx : x^3 - 3 * Real.sqrt 3 * x^2 + 9 * x - 3 * Real.sqrt 3 - 64 = 0) :
    x^6 - 8 * x^5 + 13 * x^4 - 5 * x^3 + 49 * x^2 - 137 * x + 2015 = 1898 := by
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

  have h2 : Real.sqrt 3 ^ 4 = 9 := by 
    calc 
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [h1]
      _ = 9 := by norm_num

  have eq1 : (x - Real.sqrt 3) ^ 3 = 64 := by
    nlinarith [sq_nonneg (x - Real.sqrt 3), sq_nonneg (x ^ 2 - 2 * Real.sqrt 3 * x + 3), sq_nonneg (x - 4 - Real.sqrt 3), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), sq_nonneg (Real.sqrt 3), h1, h2, hx, Real.sqrt_nonneg 3]

  have h3 : x = 4 + Real.sqrt 3 := by
    have h9 : x - Real.sqrt 3 = 4 := by
      have h11 : (x - Real.sqrt 3) ^ 3 = 4 ^ 3 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), sq_nonneg ((x - Real.sqrt 3) ^ 2), sq_nonneg ((x - Real.sqrt 3) * 4), sq_nonneg ((4 : ℝ) ^ 2), sq_nonneg (Real.sqrt 3 ^ 2)]
      have h10 : x - Real.sqrt 3 = 4 := by
        have h6 : (x - Real.sqrt 3) ^ 3 = (4 : ℝ) ^ 3 := by linarith
        have h7 : x - Real.sqrt 3 = 4 := by
          have h8 : (x - Real.sqrt 3) ^ 3 = (4 : ℝ) ^ 3 := by linarith
          have h3a : (x - Real.sqrt 3) ^ 3 - ((4 : ℝ) ^ 3) = 0 := by linarith
          have h4a : (x - Real.sqrt 3 - 4) * ((x - Real.sqrt 3) ^ 2 + 4 * (x - Real.sqrt 3) + 16) = 0 := by
            nlinarith [sq_nonneg ((x - Real.sqrt 3) ^ 2), sq_nonneg ((x - Real.sqrt 3) + 2), sq_nonneg ((x - Real.sqrt 3) * 4)]
          cases' (mul_eq_zero.1 h4a) with h5a h6a
          · -- Case where (x - Real.sqrt 3 - 4) = 0
            linarith
          · -- Case where the quadratic factor is zero
            nlinarith [sq_nonneg ((x - Real.sqrt 3) + 2), sq_nonneg (Real.sqrt 3 ^ 2), Real.sqrt_nonneg 3, sq_nonneg (x - 4 + Real.sqrt 3), sq_nonneg (x + 4 - Real.sqrt 3), h1]
        linarith
      linarith
    nlinarith 
  rw [h3]
  nlinarith [sq_nonneg ((4 + Real.sqrt 3) ^ 2 - 2 * (4 + Real.sqrt 3) * Real.sqrt 3 + (Real.sqrt 3) ^ 2), sq_nonneg ((4 + Real.sqrt 3) ^ 2 - 8 * (4 + Real.sqrt 3) + 16), sq_nonneg ((4 + Real.sqrt 3) ^ 2 - 2 * Real.sqrt 3 * (4 + Real.sqrt 3) + 3), sq_nonneg ((4 + Real.sqrt 3) - 4 - Real.sqrt 3), sq_nonneg (Real.sqrt 3), sq_nonneg (Real.sqrt 3 ^ 2 -3), sq_nonneg (Real.sqrt 3 ^ 4 -9), sq_nonneg ((4 + Real.sqrt 3) ^ 2 - 4 * Real.sqrt 3), sq_nonneg ((4 + Real.sqrt 3) ^ 3 - 4 * ((4 + Real.sqrt 3) ^ 3 - 64)), Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), h1, h2]