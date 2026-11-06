import Mathlib

theorem algebra_238699 (total_money : ℝ) (h : total_money = 2000) (ball_cost : ℝ)
    (doll_cost : ℝ) (h_ball_cost : ball_cost = total_money / 4) (h_doll_cost : doll_cost = (total_money - ball_cost) / 3) :
    total_money - ball_cost - doll_cost = 1000 := by
  rw [h] at h_ball_cost
  have h_ball_cost' : ball_cost = 500 := by
    rw [h_ball_cost]
    norm_num
  rw [h, h_ball_cost'] at h_doll_cost
  have h_doll_cost' : doll_cost = 500 := by
    rw [h_doll_cost]
    norm_num
  rw [h, h_ball_cost', h_doll_cost']
  all_goals norm_num