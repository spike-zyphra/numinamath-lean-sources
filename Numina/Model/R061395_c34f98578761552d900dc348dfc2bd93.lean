import Mathlib

theorem algebra_204314 (x1 x2 y1 y2 : ℝ) (h₀ : x1^2 + 5 * x2^2 = 10) (h₁ : x2 * y1 - x1 * y2 = 5)
    (h₂ : x1 * y1 + 5 * x2 * y2 = Real.sqrt 105) :
    y1^2 + 5 * y2^2 = 23 := by
  have h₃ : (x1 ^ 2 + 5 * x2 ^ 2) * (y1 ^ 2 + 5 * y2 ^ 2) =
    (x1 * y1 + 5 * x2 * y2) ^ 2 + 5 * (x2 * y1 - x1 * y2) ^ 2 := by 
    nlinarith [sq_nonneg (x1 * y2 - x2 * y1), sq_nonneg (x1 * y1 - 5 * x2 * y2), sq_nonneg (x2 * y2 * 5 - x1 * y1 * 5)]
  rw [h₀] at h₃
  have h₄ : (x1 * y1 + 5 * x2 * y2) ^ 2 + 5 * (x2 * y1 - x1 * y2) ^ 2 = 230 := by
    have h₅ : (x1 * y1 + 5 * x2 * y2) ^ 2 = 105 := by
      have h5 : (x1 * y1 + 5 * x2 * y2) = Real.sqrt 105 := by 
        linarith
      rw [h5]
      rw [Real.sq_sqrt]
      all_goals linarith
      all_goals nlinarith
    have h₆ : (x2 * y1 - x1 * y2) ^ 2 = 25 := by
      nlinarith
    nlinarith
  have h₇ : 10 * (y1 ^ 2 + 5 * y2 ^ 2) = 230 := by
    nlinarith [h₃, h₄]
  have h₈ : y1 ^ 2 + 5 * y2 ^ 2 = 23 := by
    linarith
  exact h₈
  all_goals nlinarith
  <;> nlinarith
  <;> linarith