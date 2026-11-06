import Mathlib

theorem algebra_200262 (a b c : ℝ) (h₀ : a + b + c = 2) (h₁ : a * b + a * c + b * c = 1) :
    0 ≤ a ∧ a ≤ 4 / 3 ∧ 0 ≤ b ∧ b ≤ 4 / 3 ∧ 0 ≤ c ∧ c ≤ 4 / 3 := by
  have h2 : c = 2 - a - b := by linarith 
  rw [h2] at h₁ 
  constructor
  · -- Show 0 ≤ a
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), sq_nonneg (a + b - (2 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((2 - a - b) - 1)]
  constructor
  · -- Show a ≤ 4 / 3
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), sq_nonneg (a + b - (2 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((2 - a - b) - 1)]
  constructor
  · -- Show 0 ≤ b
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), sq_nonneg (a + b - (2 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((2 - a - b) - 1)]
  constructor
  · -- Show b ≤ 4 / 3
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), sq_nonneg (a + b - (2 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((2 - a - b) - 1)]
  constructor
  · -- Show 0 ≤ c
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), sq_nonneg (a + b - (2 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((2 - a - b) - 1)]
  · -- Show c ≤ 4 / 3
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), sq_nonneg (a + b - (2 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((2 - a - b) - 1)]