import Mathlib

theorem algebra_299445 {x y : ℝ} (h1 : y = -2 * x + 3) (h2 : ∀ m : ℝ, y = m * x ^ 2 + (m - 2 / 3) * x - (2 * m - 3 / 8)) :
    (x = 1 ∧ y = 1) ∨ (x = -2 ∧ y = 7) ∨ (x = 63 / 32 ∧ y = -15 / 16) := by
  have eq3 := h2 0
  have eq4 : y = -2 / 3 * x + 3 / 8 := by
    linarith
  have eq5 : x = 63 / 32 := by
    linarith [h1, eq4]
  have eq6 : y = -15 / 16 := by
    rw [eq5] at h1
    linarith
  right
  right
  exact ⟨eq5, eq6⟩