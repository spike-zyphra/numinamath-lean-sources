import Mathlib

theorem algebra_21806 (a : ℕ → ℚ) (ha : a 0 = 1) (h : ∀ n, a (n + 1) = a n / 2) :
    a 4 + a 5 = 3 / 32 := by 
  have ha1 : a 1 = 1 / 2 := by
    rw [h 0, ha]
    all_goals norm_num
  have ha2 : a 2 = 1 / 4 := by 
    rw [h 1, ha1]
    all_goals norm_num
  have ha3 : a 3 = 1 / 8 := by 
    rw [h 2, ha2]
    all_goals norm_num
  have ha4 : a 4 = 1 / 16 := by 
    rw [h 3, ha3]
    all_goals norm_num
  have ha5 : a 5 = 1 / 32 := by 
    rw [h 4, ha4]
    all_goals norm_num
  rw [ha4, ha5]
  all_goals norm_num