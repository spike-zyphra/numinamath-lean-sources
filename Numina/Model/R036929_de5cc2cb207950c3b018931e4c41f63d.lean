import Mathlib

theorem algebra_70690 {a b c d : ℤ} (h : ∀ x > 0, ∃ q : ℚ, (a * x + b) / (c * x + d) = q) :
    ∃ A B C D : ℤ, ∀ x > 0, (a * x + b) / (c * x + d) = (A * x + B) / (C * x + D) := by 
  use a, b, c, d
  intro x hx
  rfl