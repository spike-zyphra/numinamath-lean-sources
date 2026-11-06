import Mathlib

theorem algebra_75 (a b c d : ℚ) (h₀ : a + (b + c + d) / 3 = 92) (h₁ : b + (a + c + d) / 3 = 86) (h₂ : c + (a + b + d) / 3 = 80)
(h₃ : d + (a + b + c) / 3 = 90) :
max (max a b) (max c d) = 51 := by
  have eq1 : 3 * a + b + c + d = 276 := by 
    linarith [h₀]
  have eq2 : 3 * b + a + c + d = 258 := by 
    linarith [h₁]
  have eq3 : 3 * c + a + b + d = 240 := by 
    linarith [h₂]
  have eq4 : 3 * d + a + b + c = 270 := by 
    linarith [h₃]
  have h_sum : a + b + c + d = 174 := by
    linarith [eq1, eq2, eq3, eq4]
  have ha : a = 51 := by 
    linarith [eq1, h_sum]
  have hb : b = 42 := by 
    linarith [eq2, h_sum]
  have hc : c = 33 := by 
    linarith [eq3, h_sum]
  have hd : d = 48 := by 
    linarith [eq4, h_sum]
  rw [ha, hb, hc, hd]
  norm_num [max_eq_left_of_lt, max_eq_right_of_lt]