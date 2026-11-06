import Mathlib

theorem algebra_234613 (h : ∃ x y, x > 0 ∧ y > 0 ∧ x * 11 = y * 12 ∧ y * 11 = x * 12 + 6) :
    x = 54.54 ∧ y = 65.55 := by
  rcases h with ⟨x, y, hx_pos, hy_pos, heq1, heq2⟩
  have eq3 : x = 12 / 11 * y := by
    nlinarith
  have eq4 : 11 * y = 12 * x + 6 := by
    nlinarith
  rw [eq3] at eq4
  nlinarith