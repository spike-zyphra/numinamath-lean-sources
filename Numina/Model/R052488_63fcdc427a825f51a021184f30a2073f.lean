import Mathlib

theorem algebra_15890 (total_cookies : ℕ) (h : total_cookies = 8 + 10 + 12 + 15 + 16 + 17 + 20) :
    total_cookies / 7 = 14 := by 
  calc
    total_cookies / 7 = (8 + 10 + 12 + 15 + 16 + 17 + 20) / 7 := by rw [h]
    _ = 98 / 7 := by norm_num
    _ = 14 := by norm_num