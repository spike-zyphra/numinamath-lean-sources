import Mathlib.Tactic

theorem alg_1175
  (j b c d h : ℚ)
  (john_speed : j = 3)
  (bob_speed : b = 5)
  (catchup_speed_bob : c = b - j)
  (distance_between_them : d = 1)
  (hour_needed : h = d / c) :
  h = 1/2 := by
  rw [hour_needed, distance_between_them, catchup_speed_bob, bob_speed, john_speed]
  all_goals norm_num