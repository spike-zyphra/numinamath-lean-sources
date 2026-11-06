import Mathlib

theorem algebra_324073 {a b c : ℝ} (h1 : c + b = 3 * a ^ 2 - 4 * a + 6) (h2 : c - b = a ^ 2 - 4 * a + 4) :
    a < b ∧ b ≤ c := by 
  have eq1 : b = a^2 + 1 := by
    nlinarith [h1, h2]
  have eq2 : c = 2 * a^2 - 4 * a + 5 := by
    nlinarith [h1, h2]
  have h3 : a < b := by
    rw [eq1]
    nlinarith [sq_nonneg (a - 1 / 2)]
  have h4 : b ≤ c := by
    rw [eq1, eq2]
    nlinarith [sq_nonneg (a - 2)]
  exact ⟨h3, h4⟩