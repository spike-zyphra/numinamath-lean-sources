import Mathlib

theorem algebra_194702 {x y : ℝ} (h₀ : x + y = 22500) (h₁ : (1 + 40 / 100) * (x + y) = (1 + 25 / 100) * x + (1 + 50 / 100) * y) :
    x = 9000 ∧ y = 13500 := by 
  have eq1 : x = 9000 := by
    nlinarith
  have eq2 : y = 13500 := by 
    linarith [h₀, eq1]
  exact ⟨eq1, eq2⟩