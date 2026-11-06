import Mathlib

theorem algebra_323624 : √(1991 * 1993 * 1995 * 1997 + 16) = 3976031 := by
  have h1 : (1991 * 1993 * 1995 * 1997 + 16 : ℝ) = (3976031 : ℝ) ^ 2 := by
    norm_num
  rw [h1]
  exact Real.sqrt_sq (by norm_num)