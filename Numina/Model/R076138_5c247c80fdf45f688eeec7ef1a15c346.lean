import Mathlib

theorem algebra_280954 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (hxy : x - y / 2 = 3 * (x - y) / 2) :
    max x y / min x y = 2 := by
  have h1 : x = 2 * y := by
    linarith
  have h2 : max x y = x := by
    rw [max_eq_left_iff]
    nlinarith
  have h3 : min x y = y := by
    rw [min_eq_right_iff]
    nlinarith
  rw [h2, h3]
  have h4 : x / y = 2 := by
    rw [show x = 2 * y by linarith [h1]]
    field_simp
    <;> nlinarith
  linarith [h4]