import Mathlib

theorem algebra_21436 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  have eq1 : 4 * d = 30 := by 
    linarith
  have hd : d = (30 / 4 : ℝ) := by 
    linarith
  have eq2 : a = -15 := by
    rw [hd] at h₀
    linarith
  rw [eq2, hd]
  norm_num