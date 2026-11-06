import Mathlib

theorem algebra_10706 {B : ℝ × ℝ} (h : (2, 5) = midpoint ℝ (3, 1) B) :
    B.1 * B.2 = 9 := by
  simp [midpoint_eq_smul_add, Prod.ext_iff] at h
  have hx : B.1 = 1 := by 
    linarith
  have hy : B.2 = 9 := by 
    linarith 
  rw [hx, hy]
  all_goals norm_num