import Mathlib

theorem inequalities_234834 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x > y) (h : 1 > x) :
    (x - y) / (1 - x * y) < 1 := by 
  have h1 : 1 - x * y > 0 := by 
    nlinarith [show 0 < y from hy, show 0 < x from hx, show x < 1 from by linarith, mul_pos hx hy, sq_nonneg (x - 1), sq_nonneg (y - 1)]
  apply (div_lt_iff (by linarith)).mpr
  nlinarith [show 0 < x from hx, show 0 < y from hy, show x > y from hxy, show 0 < 1 - x by nlinarith, mul_pos hx hy, sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  all_goals nlinarith [show 0 < x from hx, show 0 < y from hy, show x > y from hxy, show 0 < 1 - x by nlinarith, mul_pos hx hy, sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]