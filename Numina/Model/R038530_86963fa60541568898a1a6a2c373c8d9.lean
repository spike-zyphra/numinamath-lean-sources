import Mathlib

theorem algebra_229825 (x : ℝ) :
    abs (x^2 - 100) = 2 * x + 1 ↔ x = 1 + Real.sqrt 102 ∨ x = 9 := by
  constructor
  · -- Assume abs (x^2 - 100) = 2 * x + 1, prove x = 1 + Real.sqrt 102 ∨ x = 9
    intro h
    by_cases h1 : x ^ 2 - 100 ≥ 0
    · -- If x^2 - 100 ≥ 0 then abs (x^2 - 100) = x^2 - 100
      have h2 : abs (x^2 - 100) = x^2 - 100 := by
        rw [abs_of_nonneg h1]
      rw [h2] at h
      have h3 : (x - 1 - Real.sqrt 102) * (x - 1 + Real.sqrt 102) = 0 := by
        nlinarith [Real.sqrt_nonneg 102, Real.sq_sqrt (show (0 : ℝ) ≤ 102 by norm_num), sq_nonneg (x - 1), sq_nonneg ((x - 1) - Real.sqrt 102), sq_nonneg (x + 1)]
      cases' (mul_eq_zero.mp h3) with h4 h5
      · -- The solution is x = 1 + sqrt 102
        left
        linarith
      · -- Show that x = 1 - Real.sqrt 102 is invalid
        nlinarith [Real.sqrt_nonneg 102, Real.sq_sqrt (show (0 : ℝ) ≤ 102 by norm_num), sq_nonneg (x + 1)]
    · -- If x^2 - 100 < 0 then abs (x^2 - 100) = 100 - x^2
      have h2 : abs (x^2 - 100) = 100 - x^2 := by
        rw [abs_of_neg (show x^2 - 100 < 0 by linarith)]
        all_goals linarith
      rw [h2] at h
      have h4 : (x - 9) * (x + 11) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- The solution is x = 9
        right
        linarith
      · -- Show that x = -11 is invalid
        nlinarith [Real.sqrt_nonneg 102, Real.sq_sqrt (show (0 : ℝ) ≤ 102 by norm_num), sq_nonneg (x - 9)]
  · -- Assume x = 1 + Real.sqrt 102 ∨ x = 9, prove abs (x^2 - 100) = 2 * x + 1
    rintro (h | h)
    · -- Case where x = 1 + Real.sqrt 102
      have h_eq : x = 1 + Real.sqrt 102 := by
        linarith [h]
      have h1 : x ^ 2 - 100 ≥ 0 := by
        rw [h_eq]
        nlinarith [Real.sqrt_nonneg 102, Real.sq_sqrt (show (0 : ℝ) ≤ 102 by norm_num)]
      have h2 : abs (x ^ 2 - 100) = x ^ 2 - 100 := by
        rw [abs_of_nonneg h1]
      rw [h2]
      nlinarith [Real.sqrt_nonneg 102, Real.sq_sqrt (show (0 : ℝ) ≤ 102 by norm_num), h_eq]
    · -- Case where x = 9
      have h_eq : x = 9 := by
        linarith [h]
      have h1 : x ^ 2 - 100 < 0 := by
        rw [h_eq]
        nlinarith
      have h2 : abs (x ^ 2 - 100) = 100 - x ^ 2 := by
        rw [abs_of_neg h1]
        all_goals linarith
      rw [h2]
      nlinarith [h_eq]