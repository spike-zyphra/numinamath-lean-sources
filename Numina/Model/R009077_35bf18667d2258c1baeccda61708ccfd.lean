import Mathlib.Tactic

theorem num_theory_1198
  (flips r_sc t_sc : ℕ)
  (miles : ℝ)
  (total_flips : flips = 44)
  (total_step_count : t_sc = flips * 100000 + r_sc)
  (remaining_step_count : r_sc = 50000)
  (total_miles : miles = t_sc / 1800 ) :
  miles = 22250 / 9 := by 
  rw [total_flips] at total_step_count
  rw [remaining_step_count] at total_step_count
  have ht_sc : t_sc = 4450000 := by
    norm_num [total_step_count]
  rw [ht_sc] at total_miles 
  rw [total_miles]
  all_goals norm_num