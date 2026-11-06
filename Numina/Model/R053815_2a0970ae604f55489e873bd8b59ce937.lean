import Mathlib

theorem algebra_19764 (x1 x2 : ℝ) (y1 y2 : ℝ)
    (h : x1 = 3 ∧ y1 = 1 ∧ x2 = 5 ∧ y2 = 1) :
    (x1 + x2) / 2 + (y1 + y2) / 2 = 5 := by
  rcases h with ⟨hx1, hy1, hx2, hy2⟩
  rw [hx1, hy1, hx2, hy2]
  norm_num