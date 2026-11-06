import Mathlib

theorem algebra_15395 (x : ℝ) (hx : x * (1 + 5 / 100)^10 = 500000) :
    round (x * 100) / 100 = (306956.63 : ℝ) := by
  have hx2 : x = 500000 / (1 + (5 / 100 : ℝ)) ^ 10 := by
    field_simp at hx ⊢
    linarith
  rw [hx2]
  norm_num [round_eq]
  all_goals norm_num