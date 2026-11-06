import Mathlib

theorem algebra_9215 (x : ℝ) : (x^2 - 3 * abs x - 2 = 0) ↔
    (x = (-3 - Real.sqrt 17) / 2) ∨ (x = (3 + Real.sqrt 17) / 2) := by
  constructor
  · -- Forward direction: if x^2 - 3*|x| - 2 = 0, then x is one of the two roots.
    intro h
    by_cases h1 : x ≥ 0
    · -- Case 1: x ≥ 0, so |x| = x.
      have h2 : abs x = x := abs_of_nonneg h1
      rw [h2] at h
      have h3 : x^2 - 3 * x - 2 = 0 := by linarith
      have h4 : (x - (3 + Real.sqrt 17) / 2) * (x - (3 - Real.sqrt 17) / 2) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
      cases' (mul_eq_zero.1 h4) with h5 h6
      · -- Case where x = (3 + sqrt 17) / 2
        right
        linarith
      · -- Case where x = (3 - sqrt 17) / 2, which contradicts x >= 0
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), Real.sqrt_nonneg 17]
    · -- Case 2: x < 0, so |x| = -x.
      have h2 : abs x = -x := abs_of_neg (lt_of_not_ge h1)
      rw [h2] at h
      have h3 : x^2 + 3 * x - 2 = 0 := by nlinarith
      have h4 : (x - (-3 + Real.sqrt 17) / 2) * (x - (-3 - Real.sqrt 17) / 2) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
      cases' (mul_eq_zero.1 h4) with h5 h6
      · -- Case where x = (-3 + sqrt 17) / 2, which contradicts x < 0
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), Real.sqrt_nonneg 17]
      · -- Case where x = (-3 - sqrt 17) / 2
        left
        linarith
  · -- Backward direction: if x is either of the two roots, then x^2 - 3*|x| - 2 = 0.
    rintro (h | h)
    · -- Case where x = (-3 - sqrt 17) / 2
      have h1 : x < 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), Real.sqrt_nonneg 17]
      have h2 : abs x = -x := abs_of_neg h1
      rw [h2]
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
    · -- Case where x = (3 + sqrt 17) / 2
      have h1 : x ≥ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), Real.sqrt_nonneg 17]
      have h2 : abs x = x := abs_of_nonneg h1
      rw [h2]
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]