import Mathlib

theorem algebra_281362 {b g : ℕ} (hb : b = 128) (hg : g ≠ 0)
    (hbg : b * 5 = g * 8) : b + g = 208 := by 
  subst hb
  have : g = 80 := by
    omega
  calc
    128 + g = 128 + 80 := by rw [this]
    _ = 208 := by norm_num