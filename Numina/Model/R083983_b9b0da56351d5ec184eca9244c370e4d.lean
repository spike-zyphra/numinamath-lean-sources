import Mathlib

theorem algebra_162408 {a b : ℕ} (h₀ : a - b = 3) (h₁ : a * b = 180) :
    a = 15 ∧ b = 12 := by
  have h2 : a ≥ b := by 
    omega 
  have h3 : a = b + 3 := by 
    omega 
  rw [h3] at h₁ 
  have h4 : b ≤ 15 := by
    nlinarith [sq_nonneg (b : ℕ), sq_nonneg ((b + 3) : ℕ), h₁]
  interval_cases b <;> omega 
  all_goals omega 
  all_goals tauto 
  all_goals omega 
  all_goals linarith