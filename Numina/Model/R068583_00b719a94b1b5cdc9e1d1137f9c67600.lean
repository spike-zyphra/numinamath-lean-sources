import Mathlib

theorem algebra_48039 {a b c : ℝ} (h : a + b + c = 0) :
    (a^2 + b^2 + c^2)^2 = 2 * (a^4 + b^4 + c^4) := by 
  have h1 : c = -(a + b) := by 
    linarith
  rw [h1]
  ring