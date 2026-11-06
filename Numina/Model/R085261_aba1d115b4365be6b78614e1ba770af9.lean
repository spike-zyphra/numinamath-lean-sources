import Mathlib

theorem algebra_237301 (x : ℝ) : abs (x + 1) = x ^ 2 + 3 * x + 1 ↔ x = 0 ∨ x = -2 - Real.sqrt 2 := by
  constructor
  · -- Forward direction: if abs (x + 1) = x ^ 2 + 3 * x + 1, then x = 0 or x = -2 - sqrt 2
    intro h_eq
    by_cases h : x + 1 ≥ 0
    · -- Case where x + 1 ≥ 0, so abs (x + 1) = x + 1.
      rw [abs_of_nonneg h] at h_eq
      have h1 : x * (x + 2) = 0 := by
        ring_nf at h_eq
        nlinarith
      cases' (mul_eq_zero.1 h1) with h2 h3
      · -- Case x = 0.
        left
        exact h2
      · -- Case x = -2.
        have h4 : x = -2 := by linarith
        rw [h4] at h
        -- Check contradiction: x + 1 ≥ 0 contradicts x = -2.
        nlinarith
    · -- Case where x + 1 < 0, so abs (x + 1) = -(x + 1).
      rw [abs_of_neg (lt_of_not_ge h)] at h_eq
      have h1 : x ^ 2 + 4 * x + 2 = 0 := by
        nlinarith
      have h2 : (x + 2 + Real.sqrt 2) * (x + 2 - Real.sqrt 2) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      cases' (mul_eq_zero.1 h2) with h3 h4
      · -- Case x = -2 - sqrt 2.
        right
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      · -- Case x = -2 + sqrt 2.
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Backward direction: if x = 0 or x = -2 - sqrt 2, then abs (x + 1) = x ^ 2 + 3 * x + 1
    rintro (h | h)
    · -- Case x = 0.
      rw [h]
      norm_num
    · -- Case x = -2 - sqrt 2.
      rw [h]
      have h1 : (-2 - Real.sqrt 2 : ℝ) + 1 < 0 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rw [abs_of_neg h1]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]