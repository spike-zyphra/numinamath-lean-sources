import Mathlib

theorem algebra_7847 {a b : ℝ} (ha : a < 0) (hb : b > 0) :
    max (max b (b + a)) (max (b - a) (a * b)) = b - a := by
  have h1 : b + a < b := by linarith
  have h3 : a * b < 0 := by nlinarith
  have h4 : b - a > b := by
    linarith
  have h5 : max b (b + a) = b := by
    apply max_eq_left
    linarith
  have h6 : max (b - a) (a * b) = b - a := by
    apply max_eq_left
    linarith
  rw [h5, h6]
  apply max_eq_right
  linarith