import Mathlib

theorem algebra_17102 : IsGreatest {x * y * (72 - 3 * x - 4 * y) | (x : ℝ) (y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : 3 * x + 4 * y < 72) } 1152 := by
  constructor
  · -- We will show that 1152 is in the set.
    use 8, 6
    norm_num
  · -- Now, we will show that 1152 is greatest in the set.
    intro z hz
    rcases hz with ⟨x, y, hx, hy, h, hz⟩
    have h1 : 72 - 3 * x - 4 * y > 0 := by linarith
    nlinarith [sq_nonneg (x - 8), sq_nonneg (y - 6), sq_nonneg ((72 - 3 * x - 4 * y) - 24), 
      mul_pos hx hy, mul_pos hx (show (72 - 3 * x - 4 * y) > 0 by linarith), 
      mul_pos hy (show (72 - 3 * x - 4 * y) > 0 by linarith), 
      sq_nonneg (3 * x - 24), sq_nonneg (4 * y - 24), sq_nonneg ((72 - 3 * x - 4 * y) - 24)]