import Mathlib

theorem algebra_18948 (P Q : ℝ × ℝ)
    (hP : P = (5, 3)) (hQ : Q = (-3, 6)) :
    midpoint ℝ P Q = (1, 9 / 2) := by
  rw [hP, hQ]
  simp [midpoint_eq_smul_add]
  all_goals norm_num [Prod.ext_iff]
  all_goals norm_num