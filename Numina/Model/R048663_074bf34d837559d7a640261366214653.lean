import Mathlib

theorem algebra_231370 (x y : ℕ) (h₀ : x + y = 17) (h₁ : 2 * x + 3 * y = 41) :
    x = 10 ∧ y = 7 := by
  have eq1 : y = 7 := by
    omega
  have eq2 : x = 10 := by
    omega
  exact ⟨eq2, eq1⟩