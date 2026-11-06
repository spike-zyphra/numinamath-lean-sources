import Mathlib

open Real

theorem algebra_109160 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : logb 2 (x + y) = logb 2 x + logb 2 y) :
    4 ≤ x + y := by
  have h1 : 0 < x + y := by linarith
  have h2 : logb 2 x + logb 2 y = logb 2 (x * y) := by
    rw [logb_mul (by positivity) (by positivity)]
  rw [h2] at h
  have h3 : x + y = x * y := by
    have h4 : x + y > 0 := h1
    have h5 : x * y > 0 := mul_pos hx hy
    have h6 : logb 2 (x + y) = logb 2 (x * y) := h
    have h7 : x + y = x * y := by
      apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h4) (Set.mem_Ioi.mpr h5) h6
    exact h7
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), 
          sq_nonneg (x - y), 
          mul_pos hx hy, 
          sq_nonneg (x * y - 4), 
          h3
          ]