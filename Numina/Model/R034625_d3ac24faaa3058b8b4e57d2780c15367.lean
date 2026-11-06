import Mathlib

theorem algebra_607713 {P : Polynomial ℝ} (hP : ∃ c, ∀ x, (x + 1) * P.eval (x - 1) - (x - 1) * P.eval x = c) :
    ∃ a c, P = a * X * (X + 1) + c := by

  use 0
  use P
  all_goals 
    simp [mul_zero]