import Mathlib

theorem algebra_4278 {a b : ℝ} (hb : b ≠ 0) (h1 : a + 1 / b = 6) (h2 : a^3 + 1 / b^3 = 180) :
    a / b = 2 := by
  have eq1 : a^3 + 1 / b^3 = (a + 1 / b) ^ 3 - 3 * (a + 1 / b) * (a / b) := by
    field_simp [hb]
    ring
  rw [h1] at eq1
  have eq2 : a^3 + 1 / b^3 = 216 - 18 * (a / b) := by
    nlinarith [eq1]
  rw [h2] at eq2
  have eq3 : 18 * (a / b) = 36 := by
    linarith
  have eq4 : a / b = 2 := by
    linarith
  exact eq4