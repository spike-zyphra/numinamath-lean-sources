import Mathlib

theorem algebra_8999 (x : ℝ) : x^2 - 4 * x - 8 = 0 ↔ x = 2 + 2 * Real.sqrt 3 ∨ x = 2 - 2 * Real.sqrt 3 := by
  constructor
  · -- Forward direction: if x^2 - 4*x - 8 = 0, then x equals either solution
    intro h
    have h1 : x^2 - 4 * x - 8 = 0 := h
    have h2 : (x - (2 + 2 * Real.sqrt 3)) * (x - (2 - 2 * Real.sqrt 3)) = 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- h3 is x - (2 + 2 * Real.sqrt 3) = 0
      left
      linarith
    · -- h4 is x - (2 - 2 * Real.sqrt 3) = 0
      right
      linarith
  · -- Backward direction: if x equals either solution, then the equation holds
    rintro (h | h)
    · -- Case where x = 2 + 2 * Real.sqrt 3
      rw [h]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · -- Case where x = 2 - 2 * Real.sqrt 3
      rw [h]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]