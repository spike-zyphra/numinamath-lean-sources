import Mathlib

theorem algebra_42109 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : (x + y) / 2 = x - y) : max x y / min x y = 3 := by 
  have h1 : x + y = 2 * (x - y) := by linarith
  have h2 : x = 3 * y := by
    linarith
  have h3 : y > 0 := hy
  have h4 : x > 0 := by linarith [h2, hy]
  have h5 : max x y = x := by
    apply max_eq_left
    nlinarith [h2, hy]
  have h6 : min x y = y := by
    apply min_eq_right
    nlinarith [h2, hy]
  rw [h5, h6]
  have h7 : x / y = 3 := by
    rw [h2]
    field_simp [hy]
    <;> nlinarith
  linarith [h7]