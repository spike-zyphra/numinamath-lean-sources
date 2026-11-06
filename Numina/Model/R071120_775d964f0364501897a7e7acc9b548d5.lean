import Mathlib

theorem algebra_323056 {x y : ℝ}
    (hx : (x - 1)^3 + 2015 * (x - 1) = -1) (hy : (y - 1)^3 + 2015 * (y - 1) = 1) : x + y = 2 := by
  -- let's compute u + v where u = x -1, v = y -1
  have eq3 : (x - 1) + (y - 1) = 0 := by
    nlinarith [sq_nonneg ((x - 1) - (y - 1)), sq_nonneg ((x - 1) + (y - 1)), sq_nonneg (x - 1 - (y - 1)), sq_nonneg (x - 1 + (y - 1)), 
      sq_nonneg (x - 1), sq_nonneg (y - 1),
      mul_pos (show (3 : ℝ) > 0 by norm_num) (show (2015 : ℝ) > 0 by norm_num)]
  -- now given u + v =0 => x + y -2 =0 => x + y =2
  linarith