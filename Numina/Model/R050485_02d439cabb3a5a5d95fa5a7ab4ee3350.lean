import Mathlib

theorem algebra_93261 (m b : ℝ) (h : m * b > 0) :
    ¬∃ x y, (x = 1997 ∧ y = 0) ∧ y = m * x + b := by
  rintro ⟨x, y, ⟨hx1, hy1⟩, hy2⟩
  have h1 : x = 1997 := hx1
  have h2 : y = 0 := hy1
  rw [h1, h2] at hy2
  have hb : b = -1997 * m := by linarith
  rw [hb] at h
  nlinarith [sq_nonneg m]