import Mathlib

theorem algebra_138200 {b g : ℕ} (hb : b + g = 32) (hg : b * 3 = g) :
    g - b = 16 := by 
  have h1 : g = b * 3 := by
    omega
  have h2 : b = 8 := by
    omega
  have h3 : g = 24 := by
    omega
  calc 
    g - b = 24 - 8 := by rw [h3, h2]
    _ = 16 := by norm_num