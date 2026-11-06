import Mathlib

theorem algebra_9540 (x : ℝ) (hx : x > 0) (h : x + 2/x = 5) :
    x^3 + 8/x^3 = 95 := by
  have h1 : x ≠ 0 := by
    linarith
  have h2 : x^3 + 8/x^3 = (x + 2/x)^3 - 3 * (x + 2/x) * (x * (2/x)) := by
    field_simp [h1]
    ring
  have h3 : x * (2/x) = 2 := by
    field_simp [h1]
    all_goals linarith
  rw [h2, h, h3]
  norm_num