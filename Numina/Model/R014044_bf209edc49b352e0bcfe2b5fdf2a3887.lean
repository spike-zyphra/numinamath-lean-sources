import Mathlib

theorem algebra_596916 {a b c : ℝ} (h₀ : a < b) (h₁ : b < c) (h₂ : a + b + c = 6) (h₃ : a * b + b * c + c * a = 9) :
    0 < a ∧ a < 1 ∧ 1 < b ∧ b < 3 ∧ 3 < c ∧ c < 4 := by

  have h4 : c = 6 - a - b := by 
    linarith

  rw [h4] at h₃

  constructor
  · -- Prove 0 < a
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - (6 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg ((6 - a - b) - 3)]

  constructor
  · -- Prove a < 1
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - (6 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg ((6 - a - b) - 3)]

  constructor
  · -- Prove 1 < b 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - (6 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg ((6 - a - b) - 3)]

  constructor
  · -- Prove b < 3 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - (6 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg ((6 - a - b) - 3)]

  constructor
  · -- Prove 3 < c 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - (6 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg ((6 - a - b) - 3)]

  · -- Prove c < 4 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - (6 - a - b)), sq_nonneg (a - (6 - a - b)), sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg ((6 - a - b) - 3)]