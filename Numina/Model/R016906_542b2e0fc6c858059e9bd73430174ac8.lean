import Mathlib

theorem algebra_306138 (f : ℝ → ℝ) (hf : f = fun x => -2 * x ^ 3 - x)
    (x1 x2 x3 : ℝ) (hsum1 : x1 + x2 > 0) (hsum2 : x2 + x3 > 0) (hsum3 : x3 + x1 > 0) :
    f x1 + f x2 + f x3 < 0 := by
  rw [hf]
  simp
  nlinarith [sq_nonneg (x1 + x2 + x3), sq_nonneg (x1 - x2), sq_nonneg (x2 - x3), sq_nonneg (x3 - x1),
          sq_nonneg (x1 * x2), sq_nonneg (x2 * x3), sq_nonneg (x3 * x1), 
          mul_pos (show (0 : ℝ) < x1 + x2 by linarith) (show (0 : ℝ) < x2 + x3 by linarith), 
          mul_pos (show (0 : ℝ) < x2 + x3 by linarith) (show (0 : ℝ) < x3 + x1 by linarith), 
          mul_pos (show (0 : ℝ) < x3 + x1 by linarith) (show (0 : ℝ) < x1 + x2 by linarith)
]