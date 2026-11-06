import Mathlib

theorem algebra_1467 {a b c d : ℚ} (h₀ : a + b + c = 2) (h₁ : a + b + d = 17)
    (h₂ : a + c + d = -1) (h₃ : b + c + d = -3) :
    a * b * c * d = -1728 := by
  have h4 : a + b + c + d = 5 := by
    linarith
  have ha : a = 8 := by 
    linarith [h₃, h4]
  have hb : b = 6 := by
    linarith [h₂, h4]
  have hc : c = -12 := by
    linarith [h₁, h4]
  have hd : d = 3 := by
    linarith [h₀, h4]
  rw [ha, hb, hc, hd]
  norm_num