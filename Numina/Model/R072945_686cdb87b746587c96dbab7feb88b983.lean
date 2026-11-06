import Mathlib

theorem algebra_81467 {a b c : ℝ} (h₀ : a + b = 20) (h₁ : b + c = 22)
    (h₂ : c + a = 2022) : (a - b) / (c - a) = 1000 := by
  have h3 : a + b + c = 1032 := by 
    linarith
  have hc : c = 1012 := by 
    linarith [h₀, h3]
  have ha : a = 1010 := by 
    linarith [h₁, h3]
  have hb : b = -990 := by 
    linarith [h₂, h3]
  have hne : c - a ≠ 0 := by 
    rw [hc, ha]
    norm_num
  have hfrac : (a - b) / (c - a) = 1000 := by 
    rw [hb, ha, hc]
    norm_num
  exact hfrac