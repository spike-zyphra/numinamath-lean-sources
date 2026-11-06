import Mathlib

theorem algebra_276215 (total_buys total_girls : ℕ) (h₀ : total_buys = 30) (h₁ : total_girls = 20)
    (h₂ : (10 / 100 : ℝ) * total_buys + (20 / 100 : ℝ) * total_girls = (x / 100 : ℝ) * (total_buys + total_girls)) :
    x = 14 := by
  rw [show (total_buys : ℝ) = 30 by exact_mod_cast h₀] at h₂
  rw [show (total_girls : ℝ) = 20 by exact_mod_cast h₁] at h₂
  norm_num at h₂ 
  have hx : (x : ℝ) = 14 := by
    linarith 
  exact_mod_cast hx