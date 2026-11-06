import Mathlib

open Real
open scoped BigOperators

theorem inequalities_195725 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) (h''' : a + b + c = 1) :
  5 * (a^2 + b^2 + c^2) + 18 * a * b * c ≥ 7 / 3 := by
  have h1 : c = 1 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg ( (1 - a - b) - 1/3),
          mul_pos ha hb, mul_pos ha (show 0 < (1 - a - b) by nlinarith),
          mul_pos hb (show 0 < (1 - a - b) by nlinarith),
          sq_nonneg (a - b), sq_nonneg (b - (1 - a - b)), sq_nonneg (a - (1 - a - b)),
          mul_nonneg (show 0 ≤ (1 - a - b) by nlinarith) (show 0 ≤ (1 - a - b) by nlinarith),
          mul_pos (show 0 < a from ha) (show 0 < a from ha),
          mul_pos (show 0 < b from hb) (show 0 < b from hb)
          ]