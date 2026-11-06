import Mathlib

theorem algebra_180891 {x y : ℝ} (h1 : 6.751*x+3.249*y=26.751) (h2 : 3.249*x+6.751*y=23.249) :
    x=3 ∧ y=2 := by
  have eq1 : y = 2 := by
    linarith
  have eq2 : x = 3 := by
    rw [eq1] at h1
    linarith
  constructor 
  · exact eq2 
  · exact eq1