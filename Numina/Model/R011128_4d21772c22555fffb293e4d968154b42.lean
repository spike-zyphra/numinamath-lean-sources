import Mathlib

theorem algebra_95292 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x + y = 5 * (x - y)) : max x y / min x y = 3 / 2 := by
  have h1 : 4 * x = 6 * y := by
    nlinarith
  have h2 : x > y := by
    nlinarith
  have h3 : max x y = x := by
    apply max_eq_left
    linarith
  have h4 : min x y = y := by
    apply min_eq_right
    linarith
  have h5 : x / y = 3 / 2 := by
    have h6 : y ≠ 0 := by linarith
    field_simp at *
    linarith
  rw [h3, h4]
  all_goals exact h5