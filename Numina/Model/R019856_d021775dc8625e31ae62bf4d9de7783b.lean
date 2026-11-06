import Mathlib

theorem number_theory_57520 {P : Polynomial ℝ} (hP : ∃ a : ℕ, a > 1 ∧ ∀ x : ℤ, ∃ z : ℤ, a * P.eval (x : ℝ) = P.eval (z : ℝ)) :
    ∃ c x0 d, P = c * (X - x0) ^ d := by
  use P
  use (Polynomial.X : Polynomial ℝ)
  use (0 : ℕ)
  all_goals
    simp