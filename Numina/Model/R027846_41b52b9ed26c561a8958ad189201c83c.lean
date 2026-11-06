import Mathlib

theorem algebra_53749 {x y : ℝ} (hy : y < x) (h1 : x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 + 2 * x * y = 40)
    (h2 : x * y + x + y = 8) : x = 3 + Real.sqrt 7 := by

  have h3 : (x * y) ^ 2 + (x + y) ^ 2 = 40 := by
    nlinarith [h1, h2]

  have h4 : x * y = 8 - (x + y) := by
    linarith

  have h5 : (x + y) ^ 2 - 8 * (x + y) + 12 = 0 := by
    rw [h4] at h3
    nlinarith

  have h6 : ( (x + y) - 6 ) * ( (x + y) - 2 ) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case x + y = 6
    have h8 : x + y = 6 := by linarith
    have h9 : x * y = 2 := by
      nlinarith [h4, h8]
    have h10 : (x - (3 + Real.sqrt 7)) * (x - (3 - Real.sqrt 7)) = 0 := by
      nlinarith [h8, h9, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (7 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- Case x = 3 + sqrt 7
      linarith
    · -- Case x = 3 - sqrt 7
      have h13 : y = 3 + Real.sqrt 7 := by
        nlinarith [h12, h8, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (7 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      have h14 : x < y := by
        nlinarith [h12, h13, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (7 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      linarith
  · -- Case x + y = 2
    have h10 : x + y = 2 := by linarith
    have h11 : x * y = 6 := by
      nlinarith [h4, h10]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x * y - 6)]