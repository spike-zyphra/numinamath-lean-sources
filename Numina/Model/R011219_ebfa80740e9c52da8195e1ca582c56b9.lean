import Mathlib

theorem algebra_227112 (total_students : ℕ) (h₀ : total_students ≠ 0)
    (h₁ : (12 / 100 : ℝ) * total_students + (32 / 100 : ℝ) * total_students + 14 = total_students) :
    total_students = 25 := by
  have h2 : (total_students : ℝ) ≠ 0 := by
    exact_mod_cast h₀
  have eq1 : (total_students : ℝ) = 25 := by
    linarith
  have h3 : total_students = 25 := by
    exact_mod_cast eq1
  exact h3