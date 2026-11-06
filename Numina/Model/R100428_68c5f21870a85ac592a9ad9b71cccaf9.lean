import Mathlib

theorem algebra_320915 (x : ℝ) : x = (x ^ 2 - 2) ^ 2 - 2 ↔
    x = 2 ∨ x = -1 ∨ x = (-1 + Real.sqrt 5) / 2 ∨ x = (-1 - Real.sqrt 5) / 2 := by
  constructor
  · -- Forward direction: Assume x = (x^2 - 2)^2 - 2, prove x is one of the solutions
    intro h
    have h₁ : (x ^ 2 - 2) ^ 2 - x - 2 = 0 := by linarith
    have h₂ : (x - 2) * (x + 1) * (x ^ 2 + x - 1) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (x + 1), sq_nonneg (x - 2)]
    cases' (mul_eq_zero.mp h₂) with h₃ h₄
    · cases' (mul_eq_zero.mp h₃) with h₅ h₆
      · -- Case where x - 2 = 0, so x = 2
        left
        linarith
      · -- Case where x + 1 = 0, so x = -1
        right
        left
        linarith
    · -- Case where x^2 + x - 1 = 0
      have h₇ : x ^ 2 + x - 1 = 0 := by linarith
      have h₈ : (x - (-1 + Real.sqrt 5) / 2) * (x - (-1 - Real.sqrt 5) / 2) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h₈) with h₉ h₁₀
      · -- First factor equals zero
        right
        right
        left
        linarith
      · -- Second factor equals zero
        right
        right
        right
        linarith
  · -- Backward direction: Assume x is a solution, prove x = (x^2 - 2)^2 - 2
    rintro (h | h | h | h)
    · -- Case x = 2
      rw [h]
      norm_num
    · -- Case x = -1
      rw [h]
      norm_num
    · -- Case x = (-1 + √5)/2
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    · -- Case x = (-1 - √5)/2
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]