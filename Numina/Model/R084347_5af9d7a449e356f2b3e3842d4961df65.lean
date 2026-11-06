import Mathlib

theorem algebra_317048 (m : ℝ) (h : ∃ x y, x > 0 ∧ y > 0 ∧ x - y = 2 ∧ m * x + y = 3) :
    -1 < m ∧ m < 3 / 2 := by
  rcases h with ⟨x, y, hx, hy, h1, h2⟩

  have hy_eq : y = x - 2 := by linarith [h1]

  rw [hy_eq] at h2

  have h3 : m * x + (x - 2) = 3 := h2

  have h4 : (m + 1) * x = 5 := by linarith [h3]

  have h5 : m + 1 > 0 := by
    nlinarith [show x > 0 by linarith [hx], h4]

  have h8 : x > 2 := by linarith [show x > 0 by linarith [hx], show y > 0 by linarith [hy], h1]

  have h9 : m + 1 < 5 / 2 := by
    nlinarith [show (m + 1) * x = 5 by linarith, h8, h5]

  constructor
  · -- Show that $-1 < m$
    linarith
  · -- Show that $m < 3 / 2$
    nlinarith