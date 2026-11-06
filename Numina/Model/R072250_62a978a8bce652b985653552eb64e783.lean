import Mathlib

theorem algebra_197338 (v_b v_c : ℝ) (h_v : v_b > 0) (h_c : v_c > 0)
    (h_d : 37 / v_b = 37 / v_c + 2 * (7.58 - 7.18)) (h_d' : 37 / v_b = 37 / v_c + 2 * (8.19 - 7.48))
    (h_c' : 37 / v_b = 37 / v_c + 2 * (7.28 - 7.18)) :
    v_b = 42 ∧ v_c = 42 := by
  norm_num at h_d h_d' h_c'
  all_goals 
    linarith
  all_goals
    linarith