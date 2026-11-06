import Mathlib

theorem algebra_13987 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h₀ : a^2 = 16) (h₁ : b^2 = 49) (h₂ : c^2 = 169) :
    (a + b + c) / 3 = 8 := by 
  have ha1 : a = 4 := by 
    nlinarith
  have hb1 : b = 7 := by
    nlinarith
  have hc1 : c = 13 := by 
    nlinarith
  rw [ha1, hb1, hc1]
  norm_num