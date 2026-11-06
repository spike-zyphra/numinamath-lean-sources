import Mathlib

theorem algebra_248899 : ∃ f : ℕ → ℕ, ∀ n, f (f n) = f (n + 1) - f n := by
  use fun n => 0
  intro n
  simp
  all_goals omega