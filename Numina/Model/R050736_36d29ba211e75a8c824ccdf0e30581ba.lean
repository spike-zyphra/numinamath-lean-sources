import Mathlib

theorem algebra_128425 (total_students : ℕ) (h₀ : total_students < 1000)
    (h₁ : 230 + (total_students - 230) * (13 / 46 : ℚ) = total_students * (2 / 5 : ℚ) - 10) :
    total_students = 590 := by
  have h2 : (total_students : ℚ) < 1000 := by exact_mod_cast h₀
  have h3 : (total_students : ℚ) = 590 := by
    linarith
  have h4 : total_students = 590 := by
    exact_mod_cast h3
  exact h4