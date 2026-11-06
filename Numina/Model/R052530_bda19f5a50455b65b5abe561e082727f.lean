import Mathlib

noncomputable def sqrt (x : ℝ) : ℝ := if x ≥ 0 then Real.sqrt x else -(-x).sqrt

theorem algebra_209 : sqrt (36 + 64) - sqrt (25 - 16) = 7 := by
  have h1 : sqrt (36 + 64) = 10 := by
    unfold sqrt
    norm_num [Real.sqrt_eq_iff_sq_eq]
    all_goals norm_num
  have h2 : sqrt (25 - 16) = 3 := by
    unfold sqrt
    norm_num [Real.sqrt_eq_iff_sq_eq]
    all_goals norm_num
  rw [h1, h2]
  all_goals norm_num