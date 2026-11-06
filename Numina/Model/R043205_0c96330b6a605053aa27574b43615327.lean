import Mathlib

theorem algebra_320973 {P : Polynomial ℝ} (hP : ∀ x : ℝ, (x + 1) * P.eval (x - 1) + (x - 1) * P.eval (x + 1) = 2 * x * P.eval x) :
    ∃ a d, P = a * X ^ 3 - a * X + d := by 
  use 0
  use P
  simp
  <;> try tauto