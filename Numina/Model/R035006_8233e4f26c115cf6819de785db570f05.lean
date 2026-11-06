import Mathlib

theorem algebra_309044 (a b c : ℝ) (h₀ : a * b * c = 4) (h₁ : a + b + c = 2)
    (h₂ : a ≥ b ∧ b ≥ c) :
    abs a + abs b + abs c ≥ 6 := by
  by_cases ha : a ≥ 0
  · -- Case where a ≥ 0
    by_cases hb : b ≥ 0
    · -- Case where a ≥ 0 and b ≥ 0
      have hc : c ≥ 0 := by
        nlinarith [mul_nonneg ha hb, h₀]
      have h4 : a * b * c = 4 := h₀
      have h5 : a + b + c = 2 := h₁
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
                mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
    · -- Case where a ≥ 0 and b < 0
      have hc : c < 0 := by
        nlinarith [show b * c > 0 by nlinarith [h₀, mul_nonneg ha (show (0 : ℝ) ≤ -b by nlinarith)], hb]
      have h4 : abs a + abs b + abs c = a - (b + c) := by
        rw [abs_of_nonneg ha, abs_of_neg (show b < 0 by linarith), abs_of_neg (show c < 0 by linarith)]
        all_goals nlinarith
      nlinarith [sq_nonneg (b - c), sq_nonneg (a + (b + c)), sq_nonneg (a - 4), sq_nonneg (b + 1), sq_nonneg (c + 1), h₀, h₁]
  · -- Case where a < 0
    have hb : b < 0 := by
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c), h₀, h₁]
    have hc : c < 0 := by
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c), h₀, h₁]
    have h4 : abs a + abs b + abs c = - (a + b + c) := by
      rw [abs_of_neg (show a < 0 by linarith), abs_of_neg (show b < 0 by linarith), abs_of_neg (show c < 0 by linarith)]
      all_goals nlinarith
    nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1), h₀, h₁]