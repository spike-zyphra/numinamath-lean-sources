import Mathlib

theorem algebra_276215 (total_buys total_girls : ℕ) (h₀ : total_buys = 30) (h₁ : total_girls = 20)
    (h₂ : (10 / 100 : ℝ) * total_buys + (20 / 100 : ℝ) * total_girls = (x / 100 : ℝ) * (total_buys + total_girls)) :
    x = 14 := by 
  have h3 : (total_buys : ℝ) = 30 := by
    exact_mod_cast h₀
  have h4 : (total_girls : ℝ) = 20 := by
    exact_mod_cast h₁
  rw [h3, h4] at h₂
  norm_num at h₂
  linarith