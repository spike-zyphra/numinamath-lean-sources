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

  have h1: s0 = 40 := by
    rw [distance_A_B_eq_103km, remain_23km_longer_than]
      at certain_distance_add_remain_eq_whole_distance
    linarith only [certain_distance_add_remain_eq_whole_distance]

  have h2: s1 = 63 := by
    rw [remain_23km_longer_than, h1]
    norm_num

  have h3: v0 * t0 = 40 := by
    rw [← distance_eq_velocity_mul_time_0, h1]

  have h4: (v0 + 4) * (t0 + 1/4) = 63 := by
    rw [← min_15_eq_one_div_four_hour,
    ← remain_distance_time_15min_more_than_before,
    ← v1_4_greater_than_v0, ← h2,
    distance_eq_velocity_mul_time_1]

  replace h4: v0/4 + 4*t0 = 22 := by
    linarith only [h4, h3]

  replace h4: (v0 - 80) * (v0 - 8) = 0 := by
    have: v0 * (v0/4) + 4 * 40 = v0 * 22 := by
      rw [← h4, mul_add, ← h3]
      ring
    linarith only [this]

  rcases (mul_eq_zero.mp h4) with hh | hh
  · left; linarith only [hh]
  · right; linarith only [hh]