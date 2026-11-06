import Mathlib

theorem algebra_20556 (x0 y0 x1 y1 x2 : ℝ) (hx : x0 = 0) (hy : y0 = 0)
    (h1 : x1 = x0 + (1 / 2)) (h2 : y1 = y0 + (3 / 4)) (h3 : x2 = x1 + (1 / 2)) :
    Real.sqrt (x2 ^ 2 + y1 ^ 2) = 1.25 := by
  have hx1 : x1 = 1 / 2 := by
    rw [h1, hx]
    all_goals norm_num
  have hx2 : x2 = 1 := by
    rw [h3, hx1]
    all_goals norm_num
  have hy1 : y1 = 3 / 4 := by
    rw [h2, hy]
    all_goals norm_num
  rw [hx2, hy1]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> ring_nf <;> norm_num