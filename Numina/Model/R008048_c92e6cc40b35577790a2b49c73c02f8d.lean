import Mathlib

theorem algebra_13265 (total_players : ℕ) (h : total_players = 12) (taking_biology : ℕ) (h_biology : taking_biology = 7) (taking_both : ℕ) (h_both : taking_both = 2) :
    total_players - taking_biology + taking_both = 7 := by 
  calc 
    total_players - taking_biology + taking_both = 12 - 7 + 2 := by 
      rw [h, h_biology, h_both]
    _ = 5 + 2 := by 
      norm_num 
    _ = 7 := by 
      norm_num