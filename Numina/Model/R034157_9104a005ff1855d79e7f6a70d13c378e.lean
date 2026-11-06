import Mathlib

theorem algebra_9188 {x : ℝ}: 2*x^2-4*x-5 = 0 ↔ x = (2+√14)/2 ∨ x = (2-√14)/2 := by
  constructor
  · -- Assume 2x^2 - 4x - 5 = 0, prove x = (2 + √14)/2 ∨ x = (2 - √14)/2
    intro h
    have h1 : 2 * x ^ 2 - 4 * x - 5 = 0 := h
    have h2 : (x - (2 + Real.sqrt 14) / 2) * (x - (2 - Real.sqrt 14) / 2) = 0 := by
      nlinarith [h1, Real.sqrt_nonneg 14, Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where x = (2 + √14)/2
      left
      linarith
    · -- Case where x = (2 - √14)/2
      right
      linarith
  · -- Assume x = (2 + √14)/2 ∨ x = (2 - √14)/2, prove 2x^2 - 4x - 5 = 0
    rintro (h | h)
    · -- Case where x = (2 + √14)/2
      rw [h]
      nlinarith [Real.sqrt_nonneg 14, Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)]
    · -- Case where x = (2 - √14)/2
      rw [h]
      nlinarith [Real.sqrt_nonneg 14, Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)]