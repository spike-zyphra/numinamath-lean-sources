import Mathlib

theorem algebra_237895 {a b c : ℝ} (h₀ : a + b + c = a + 5 / 2) (h₁ : a + b + c = b + 59 / 6)
    (h₂ : a + b + c = c + 5 / 3) :
    a = 9 / 2 ∧ b = -17 / 6 ∧ c = 16 / 3 := by

  have eq1 : b + c = 5 / 2 := by
    linarith

  have eq2 : a + c = 59 / 6 := by
    linarith

  have eq3 : a + b = 5 / 3 := by
    linarith

  have eq4 : a = 9 / 2 := by
    linarith [eq1, eq2, eq3]

  have eq5 : c = 16 / 3 := by
    linarith [eq4, eq2]

  have eq6 : b = -17 / 6 := by
    linarith [eq4, eq3]

  exact ⟨eq4, eq6, eq5⟩