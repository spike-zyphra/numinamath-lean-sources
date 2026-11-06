import Mathlib

theorem inequalities_158291 (x : ℝ) (hx : x > 0) :
    (1 + x + x ^ 2) * (1 + x + x ^ 2 + x ^ 3 + x ^ 4) ≤ (1 + x + x ^ 2 + x ^ 3) ^ 2 := by 
  nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 1), sq_nonneg (x ^ 3), sq_nonneg (x ^ 2 - x), sq_nonneg (x - 1), 
          mul_pos hx (show 0 < x by linarith)]