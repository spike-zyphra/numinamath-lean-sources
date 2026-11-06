import Mathlib

open Real
open scoped BigOperators

theorem inequalities_201055 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (h''' : a + b + c = 1) :
  5 * (a^2 + b^2 + c^2) + 18 * a * b * c ≥ 7 / 3 := by
  have h1 : c = 1 - a - b := by
    linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_pos ha hb, mul_pos ha (show (1 - a - b) > 0 by nlinarith), 
          mul_pos hb (show (1 - a - b) > 0 by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < (1 - a - b) by nlinarith)]