import Mathlib

theorem algebra_234479 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a / 2 / 5 + a / 2 / 4 = b / 2 / 5 + b / 2 / 4) :
    2 * a / 9 < 9 * a / 40 := by
  have h3 : (2 / 9 : ℝ) < (9 / 40 : ℝ) := by norm_num
  have h4 : 0 < (a : ℝ) := by linarith
  have h5 : (2 / 9 : ℝ) * a < (9 / 40 : ℝ) * a := by
    apply mul_lt_mul_of_pos_right
    exact h3
    linarith
  linarith