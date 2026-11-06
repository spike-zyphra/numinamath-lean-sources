import Mathlib

theorem number_theory_35666 {n : ℤ} (hn : ∃ a b, n = a^2 + a * b + b^2) :
    ∃ x y, 7 * n = x^2 + x * y + y^2 := by 
  rcases hn with ⟨a, b, hn⟩
  have h1 : 7 * n = 7 * (a^2 + a * b + b^2) := by 
    rw [hn]
  use 2 * a + 3 * b, a - 2 * b
  nlinarith