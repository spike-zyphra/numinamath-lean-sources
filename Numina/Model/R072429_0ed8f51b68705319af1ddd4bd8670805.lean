import Mathlib

theorem algebra_12602 (a : ℕ → ℕ) (ha : ∀ n, a n = if n = 0 then 7 else 2 * a (n - 1)) :
    a 0 + a 1 + a 2 + a 3 + a 4 = 217 := by
  have ha0 : a 0 = 7 := by 
    simp [ha]

  have ha1 : a 1 = 14 := by 
    simp [ha, ha0]
    all_goals omega

  have ha2 : a 2 = 28 := by 
    simp [ha, ha1]
    all_goals omega

  have ha3 : a 3 = 56 := by 
    simp [ha, ha2]
    all_goals omega

  have ha4 : a 4 = 112 := by 
    simp [ha, ha3]
    all_goals omega

  calc 
    a 0 + a 1 + a 2 + a 3 + a 4 = 7 + 14 + 28 + 56 + 112 := by 
      rw [ha0, ha1, ha2, ha3, ha4]
    _ = 217 := by 
      norm_num