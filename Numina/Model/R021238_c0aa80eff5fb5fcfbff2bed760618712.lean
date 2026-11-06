import Mathlib

theorem inequalities_51760 (n : ℕ) (h₀ : 15 ∣ n) :
    (1 - 7 / 15 : ℚ) * n ≥ (8 / 15 : ℚ) * n := by
  have h1 : (1 - 7 / 15 : ℚ) = (8 / 15 : ℚ) := by
    norm_num
  rw [h1]
  all_goals 
    linarith