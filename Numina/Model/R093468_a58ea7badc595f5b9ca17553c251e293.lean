import Mathlib

open Real
open scoped BigOperators

theorem algebra_214503 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^4 + b^4 + c^4 - 2*a^2*b^2 - 2*b^2*c^2 - 2*c^2*a^2 < 0 := by 
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
    sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
    mul_pos (show 0 < a + b - c from by linarith) (show 0 < a + c - b from by linarith), 
    mul_pos (show 0 < a + c - b from by linarith) (show 0 < b + c - a from by linarith), 
    mul_pos (show 0 < b + c - a from by linarith) (show 0 < a + b - c from by linarith)
  ]