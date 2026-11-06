import Mathlib

theorem algebra_13734 (p1 p2 : ℝ × ℝ) (hp1 : p1 = (2, 2)) (hp2 : p2 = (-1, -1)) :
    Real.sqrt ((p1.1 - p2.1)^2 + (p1.2 - p2.2)^2) = 3 * Real.sqrt 2 := by
  rw [hp1, hp2]
  have h1 : Real.sqrt ((2 - -1 : ℝ) ^ 2 + (2 - -1 : ℝ) ^ 2) = Real.sqrt 18 := by
    norm_num
  have h2 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
    all_goals linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  rw [h1, h2]
  all_goals norm_num
  <;> ring_nf <;> norm_num
  all_goals linarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 18]