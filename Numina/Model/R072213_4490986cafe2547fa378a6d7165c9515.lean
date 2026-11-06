import Mathlib

theorem algebra_10717 {a d : ℤ} (h₀ : a + 15 * d = 8) (h₁ : a + 16 * d = 10) :
    a + d = -20 := by
  have hd : d = 2 := by 
    linarith
  have ha : a = -22 := by 
    rw [hd] at h₀
    linarith
  rw [ha, hd]
  all_goals linarith