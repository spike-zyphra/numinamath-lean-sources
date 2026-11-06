import Mathlib

theorem algebra_268297 (h : 0 < 180) (a b : ℝ)
    (ha : 0 < a ∧ a = 180 / 1) 
    (hb : 0 < b ∧ b = a - (10 / (5/60))) :
    180 / b = 3 := by 
  rcases ha with ⟨ha_pos, ha_eq⟩
  rcases hb with ⟨hb_pos, hb_eq⟩
  have ha' : a = 180 := by
    rw [ha_eq]
    norm_num
  have hb' : b = 60 := by 
    rw [hb_eq, ha']
    norm_num
  rw [hb']
  all_goals norm_num