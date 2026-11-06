import Mathlib

theorem algebra_176183 (v0 v1 s0 s1 t0 t1 min15 dist_A_B: ℝ)
  (distance_A_B_eq_103km: dist_A_B = 103)
  (v1_4_greater_than_v0: v1 = v0 + 4)
  (certain_distance_add_remain_eq_whole_distance: s0 + s1 = dist_A_B)
  (remain_23km_longer_than: s1 = s0 + 23)
  (min_15_eq_one_div_four_hour: min15 = 1/4)
  (remain_distance_time_15min_more_than_before: t1 = t0 + min15)
  (distance_eq_velocity_mul_time_0: s0 = v0 * t0)
  (distance_eq_velocity_mul_time_1: s1 = v1 * t1):
    v0 = 80 ∨ v0 = 8 := by
  rw [distance_A_B_eq_103km] at certain_distance_add_remain_eq_whole_distance
  have h1 : s0 = 40 := by
    linarith [certain_distance_add_remain_eq_whole_distance, remain_23km_longer_than]
  have h2 : s1 = 63 := by
    linarith [h1, remain_23km_longer_than]
  rw [h1] at distance_eq_velocity_mul_time_0
  rw [h2] at distance_eq_velocity_mul_time_1
  rw [v1_4_greater_than_v0] at distance_eq_velocity_mul_time_1
  rw [min_15_eq_one_div_four_hour] at remain_distance_time_15min_more_than_before
  have h3 : v0 * t0 = (40 : ℝ) := by linarith [distance_eq_velocity_mul_time_0]
  have h4 : (v0 + 4) * t1 = (63 : ℝ) := by linarith [distance_eq_velocity_mul_time_1]
  have h5 : t1 = t0 + (1 / 4 : ℝ) := by linarith [remain_distance_time_15min_more_than_before]
  have h6 : v0 ≠ 0 := by
    by_contra h
    rw [h] at h3
    nlinarith
  have h7 : t0 = (40 / v0 : ℝ) := by
    have h8 : v0 * t0 = (40 : ℝ) := by linarith [distance_eq_velocity_mul_time_0]
    field_simp [(show v0 ≠ 0 by assumption)]
    linarith
  have eq1 : (v0 + 4) * (40 / v0 + (1 / 4 : ℝ)) = (63 : ℝ) := by
    have eq2 : t1 = (40 / v0 + (1 / 4 : ℝ)) := by
      nlinarith [h5, h7]
    rw [eq2] at h4
    all_goals linarith
  have eq2 : v0^2 - 88 * v0 + (640 : ℝ) = 0 := by
    have eq3 : (v0 + 4) * (40 / v0 + (1 / 4 : ℝ)) = (63 : ℝ) := by
      linarith [eq1]
    have h8 : v0 ≠ 0 := h6
    field_simp [h8] at eq3
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < 2 by norm_num), sq_nonneg (v0 - 80), sq_nonneg (v0 - 8)]
  have h9 : (v0 - (80 : ℝ)) * (v0 - (8 : ℝ)) = 0 := by
    nlinarith [eq2]
  cases' (mul_eq_zero.1 h9) with h10 h11
  · left
    linarith [h10]
  · right
    linarith [h11]