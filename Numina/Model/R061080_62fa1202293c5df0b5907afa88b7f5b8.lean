import Mathlib

theorem algebra_2663 (a b c d : ℕ) (h₀ : a + b + c = 180) (h₁ : a + b + d = 197) (h₂ : a + c + d = 208)
    (h₃ : b + c + d = 222) :
    max (max a b) (max c d) = 89 := by
  have h4 : a + b + c + d = 269 := by
    omega
  have hd : d = 89 := by
    omega
  have hc : c = 72 := by
    omega
  have hb : b = 61 := by
    omega
  have ha : a = 47 := by
    omega
  simp [ha, hb, hc, hd]