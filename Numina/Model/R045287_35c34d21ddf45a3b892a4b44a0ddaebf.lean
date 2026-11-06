import Mathlib

theorem algebra_11822 : IsGreatest {(x ^ 2 + y ^ 2) | (x : ℝ) (y : ℝ) (h : 5 * x ^ 2 + 4 * y ^ 2 = 10 * x)} 4 := by
  constructor
  · -- Show that 4 belongs to the set
    use 2, 0
    norm_num
  · -- Show that any r in the set is at most 4
    intro r hr
    rcases hr with ⟨x, y, h_eq, hr⟩
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y), sq_nonneg (x - 1), sq_nonneg (y), sq_nonneg (x - 2 * y), sq_nonneg (2 * x - 5 * y), sq_nonneg (x - 2), sq_nonneg (y - 0), sq_nonneg ((x - 2) * (y)), sq_nonneg ((x - 1) * (y - 0)), sq_nonneg (x * (x - 2)), sq_nonneg (y * (y - 0)), sq_nonneg (x * y), sq_nonneg (2 * x - 4)]