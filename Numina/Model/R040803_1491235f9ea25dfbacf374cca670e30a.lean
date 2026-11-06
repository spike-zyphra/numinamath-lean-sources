import Mathlib

theorem algebra_13569 :
  IsGreatest {x * y + x * z + y * z | (x : ℝ) (y : ℝ) (z : ℝ) (h : x + 2 * y + z = 4)} 4 := by 
  constructor
  · -- First, show that 4 is in the set.
    use 2, 0, 2
    norm_num
  · -- Then, show that 4 is the greatest.
    intro s hs
    rcases hs with ⟨x, y, z, h_eq, h_s⟩
    have hz : z = 4 - x - 2 * y := by linarith
    rw [hz] at h_s
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y), sq_nonneg ((4 - x - 2 * y) - 2), sq_nonneg (x + y - 2), sq_nonneg (x - (4 - x - 2 * y)), sq_nonneg (y)]