import Mathlib

theorem number_theory_2254 (a b : ℕ) (h₀ : a < 10) (h₁ : b < 10)
    (h₂ : 2 * (300 + 10 * a + b) = 100 * a + 10 * b + 8) :
    300 + 10 * a + b = 374 := by
  have h3 : 10 * a + b = 74 := by
    omega
  have ha : a = 7 := by
    omega
  have hb : b = 4 := by
    omega
  calc
    300 + 10 * a + b = 300 + 10 * 7 + 4 := by rw [ha, hb]
    _ = 300 + 70 + 4 := by norm_num
    _ = 374 := by norm_num