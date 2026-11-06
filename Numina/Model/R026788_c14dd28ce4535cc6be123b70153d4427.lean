import Mathlib

open Real
open scoped BigOperators

theorem inequalities_306369 (x y z : ℝ) (h : x > 0) (h' : y > 0) (h'' : z > 0)
  (h''' : x + y > z) (h'''' : y + z > x) (h''''' : z + x > y) (h'''''' : x + y + z = 2) :
  x * y * z + 28 / 27 ≥ x * y + y * z + z * x := by
  have h7 : z = 2 - x - y := by linarith
  rw [h7]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - (2 - x - y)), sq_nonneg (y - (2 - x - y)), 
          sq_nonneg (x + y - (2 - x - y)), 
          mul_pos h h', 
          mul_pos h (show 0 < (2 - x - y) by linarith), 
          mul_pos h' (show 0 < (2 - x - y) by linarith), 
          mul_pos (show 0 < (2 - x - y) by linarith) (show 0 < (2 - x - y) by linarith), 
          mul_pos (sub_pos.mpr h''') (sub_pos.mpr h''''), 
          mul_pos (sub_pos.mpr h''') (sub_pos.mpr h'''''), 
          mul_pos (sub_pos.mpr h'''') (sub_pos.mpr h''''')
          ]