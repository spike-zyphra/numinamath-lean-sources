import Mathlib

theorem algebra_321531 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a * b = a + b) :
    a / b + b / a - a * b = -2 := by 
  have h1 : a / b + b / a = a * b - 2 := by
    field_simp
    nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1)]
  linarith