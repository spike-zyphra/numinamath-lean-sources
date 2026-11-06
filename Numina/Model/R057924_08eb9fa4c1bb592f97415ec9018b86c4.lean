import Mathlib

theorem algebra_19491 {a b c : ℤ} (h₀ : a + b = 8) (h₁ : b + c = -3) (h₂ : a + c = -5) :
    a * b * c = -120 := by 
  have h3 : a + b + c = 0 := by
    linarith
  have hc : c = -8 := by
    linarith [h₀, h3]
  have hb : b = 5 := by
    linarith [h₁, hc]
  have ha : a = 3 := by
    linarith [h₂, hc]
  rw [ha, hb, hc]
  norm_num