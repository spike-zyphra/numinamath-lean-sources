import Mathlib

theorem algebra_140075 (a b : ℝ) (ha : 0 < a ∧ a = 1 / 8) (hb : 0 < b ∧ b = 1 / 12)
    (h : a * 2.4 + b * 420 = 1) :
    b * 420 = 480 := by
  rcases ha with ⟨ha_pos, ha_eq⟩
  rcases hb with ⟨hb_pos, hb_eq⟩
  rw [ha_eq, hb_eq] at h
  norm_num at h
  all_goals 
    linarith