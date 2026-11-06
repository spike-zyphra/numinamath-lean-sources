import Mathlib

theorem algebra_287925 {x y : ℝ} (h₀ : x + x * y + y = 2 + 3 * √2) (h₁ : x ^ 2 + y ^ 2 = 6) :
    |x + y + 1| = 3 + √2 := by

  have h2 : (x + y) ^ 2 - 2 * (x * y) = 6 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

  have h3 : (x + y) + (x * y) = 2 + 3 * Real.sqrt 2 := by
    nlinarith
  
  have h4 : (x + y - (2 + Real.sqrt 2)) * (x + y - (-4 - Real.sqrt 2)) = 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (x - y)]

  cases' (mul_eq_zero.mp h4) with h5 h6

  · -- Case x+y = 2 + sqrt 2
    have h7 : x + y = 2 + Real.sqrt 2 := by nlinarith
    have h8 : x + y + 1 = 3 + Real.sqrt 2 := by linarith

    have h9 : |x + y + 1| = |(3 + Real.sqrt 2 : ℝ)| := by
      rw [h8]

    have h10 : |(3 + Real.sqrt 2 : ℝ)| = 3 + Real.sqrt 2 := by
      have h11 : (3 + Real.sqrt 2 : ℝ) ≥ 0 := by
        linarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

      rw [abs_of_nonneg h11]

    rw [h9, h10]
    all_goals try linarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  · -- Case x+y = -4 - sqrt 2
    have h7 : x + y = -4 - Real.sqrt 2 := by nlinarith
    have h8 : x + y + 1 = -3 - Real.sqrt 2 := by linarith
    rw [h8]

    have h9 : |-3 - Real.sqrt 2| = 3 + Real.sqrt 2 := by
      have h10 : (-3 - Real.sqrt 2) < 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 2]
      rw [abs_of_neg h10]
      all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]

    rw [h9]
    all_goals try linarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]