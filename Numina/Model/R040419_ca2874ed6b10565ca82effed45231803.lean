import Mathlib

noncomputable def f_9320 (x y : ℝ) := Real.sqrt (x + y) / (x - y)

theorem algebra_9320 : f_9320 4 8 = -Real.sqrt 3 / 2 := by 
  unfold f_9320 
  have h1 : Real.sqrt (4 + (8 : ℝ)) = 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h1]
  have h2 : (2 * Real.sqrt 3 / (4 - (8 : ℝ)) ) = - (Real.sqrt 3 / 2 ) := by
    norm_num
    <;> ring
  rw [h2]
  all_goals linarith