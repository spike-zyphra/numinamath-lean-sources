import Mathlib

open Real
open scoped BigOperators

theorem inequalities_166998 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
  (hz : 0 < z) (hsum : x + y + z = 1) :
  a * x * y + b * y * z + c * z * x ≤ (a + b + c) * (1 / 2) := by
  -- introduce variables with hsum, x + y + z = 1
  have hz' : z = 1 - x - y := by linarith
  rw [hz'] at *
  -- use squared terms introduced by x, y, z.
  -- introduced into Lean by "nlinarith" squared terms
  nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (1 - x - y - 1 / 2),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < b + c - a by linarith) (show 0 < a + b + c by linarith),
          mul_pos (show 0 < a + c - b by linarith) (show 0 < a + b + c by linarith),
          mul_pos (show 0 < a + b - c by linarith) (show 0 < a + b + c by linarith)
]