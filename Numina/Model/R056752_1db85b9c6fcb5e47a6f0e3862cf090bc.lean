import Mathlib

theorem algebra_305030 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a > b)
    (h1 : 15 * a = 15 * b + 18 * (a - b)) (h2 : 23 * a = 23 * b + 50) :
    b / a = 25 := by 
  have h3 : a = b := by 
    linarith
  linarith