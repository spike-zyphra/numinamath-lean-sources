import Mathlib

theorem algebra_96738 (a b c d : ℤ) (h₀ : a + b + c = 180) (h₁ : a + b + d = 197)
    (h₂ : a + c + d = 208) (h₃ : b + c + d = 222) :
    max (max a b) (max c d) = 89 := by 
  have h4 : a + b + c + d = 269 := by
    linarith

  have ha : a = 47 := by 
    linarith [h₃, h4]

  have hb : b = 61 := by 
    linarith [h₂, h4]

  have hc : c = 72 := by 
    linarith [h₁, h4]

  have hd : d = 89 := by 
    linarith [h₀, h4]

  simp [ha, hb, hc, hd]
  all_goals norm_num [max_eq_right, max_eq_left]