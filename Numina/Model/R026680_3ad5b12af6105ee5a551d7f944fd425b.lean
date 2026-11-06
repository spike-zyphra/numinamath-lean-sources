import Mathlib

theorem algebra_11256 {P : ℤ → ℤ}
    (hP : ∀ x, P x = x ^ 4 + 6 * x ^ 3 + 11 * x ^ 2 + 3 * x + 31) :
    ∃ x, IsSquare (P x) ∧ x = 10 := by 
  use 10
  constructor
  · -- Show that $P(10)$ is a perfect square
    rw [hP 10]
    native_decide
  · -- Show x = 10
    rfl