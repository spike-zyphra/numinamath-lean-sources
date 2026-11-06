import Mathlib

theorem algebra_3727 {x y : ℝ} (h1 : x + 4 * y = 12) (h2 : 5 * x + 2 * y = 24) :
    x = 4 ∧ y = 2 := by 
  have eq1 : y = 2 := by 
    linarith [h1, h2]
  have eq2 : x = 4 := by 
    linarith [h1, eq1]
  exact ⟨eq2, eq1⟩