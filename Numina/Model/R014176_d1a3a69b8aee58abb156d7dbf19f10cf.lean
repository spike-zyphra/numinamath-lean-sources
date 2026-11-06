import Mathlib

theorem algebra_324750 (a b c x y : ℝ) (h₀ : a ≠ 0) (h₁ : b ≠ 0) (h₂ : c ≠ 0)
    (h₃ : a * x + b * y + 2 * c = 0) (h₄ : a * b - c ^ 2 ≥ 0) :
    x * y ≤ 1 := by

  have h5 : c = - (a * x + b * y) / 2 := by
    have h6 : 2 * c = - (a * x + b * y) := by
      linarith [h₃]
    linarith

  have h6 : a * b - (- (a * x + b * y) / 2) ^ 2 ≥ 0 := by
    rw [h5] at h₄
    linarith

  have h7 : 4 * a * b ≥ (a * x + b * y) ^ 2 := by
    nlinarith [h6]

  nlinarith [sq_nonneg (x * a - y * b), sq_nonneg (a - b), sq_nonneg (x - y), 
          sq_nonneg (a * y - b * x), sq_nonneg (c), sq_pos_of_ne_zero h₂, 
          sq_nonneg (a * b), sq_nonneg (x * y), sq_nonneg (a + b), sq_nonneg (x + y), 
          sq_nonneg (a * x - b * y), sq_nonneg (a * y + b * x)
          ]