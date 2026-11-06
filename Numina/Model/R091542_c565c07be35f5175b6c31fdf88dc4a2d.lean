import Mathlib

theorem algebra_117532 {P : Polynomial ℝ} (hP : ∀ x : ℝ, P.eval (2 * x) = P.eval x) :
    ∃ c, P = c * X ^ 0 := by
  use P
  simp