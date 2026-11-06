import Mathlib

theorem algebra_32196 (a d : ℤ) (h₀ : a = 2020) (h₁ : a + 4 * d = 4040) :
    a + d = 2525 := by
  rw [h₀] at h₁ 
  have hd : d = 505 := by 
    linarith 
  rw [h₀, hd]
  all_goals norm_num