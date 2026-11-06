import Mathlib

theorem algebra_182234 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : x * 2 + y * 7 = 3 * (x + y)) :
    x / y = 4 := by
  have h1 : x = 4 * y := by
    linarith
  have h2 : x / y = 4 := by
    rw [h1]
    field_simp [ne_of_gt hy]
    all_goals nlinarith
  exact h2