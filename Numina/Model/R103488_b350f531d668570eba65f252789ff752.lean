import Mathlib

open Real
open scoped BigOperators

theorem algebra_323507 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (h''' : a + b + c = 3) :
  a^2 + b^2 + c^2 + (4/3)*a*b*c ≥ 13/3 := by 
  have h1 : c = 3 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (3 - a - b - 1), 
    sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg ((3 - a - b) - 1), 
    mul_pos ha hb, mul_pos ha (show 0 < (3 - a - b) by nlinarith), 
    mul_pos hb (show 0 < (3 - a - b) by nlinarith)]