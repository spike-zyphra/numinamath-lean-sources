import Mathlib

theorem algebra_238882 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + (b + c + d) / 3 = 17) (h2 : b + (a + c + d) / 3 = 21) (h3 : c + (a + b + d) / 3 = 23)
    (h4 : d + (a + b + c) / 3 = 29) :
    max (max a b) (max c d) = 21 := by 
  have h_sum : a + b + c + d = 45 := by 
    linarith
  
  have ha1 : a = 3 := by 
    have eq1 : 3 * a + b + c + d = 51 := by 
      linarith [h1, h_sum]
    linarith [eq1, h_sum]

  have hb1 : b = 9 := by 
    have eq2 : 3 * b + a + c + d = 63 := by 
      linarith [h2, h_sum]
    linarith [eq2, h_sum]

  have hc1 : c = 12 := by 
    have eq3 : 3 * c + a + b + d = 69 := by 
      linarith [h3, h_sum]
    linarith [eq3, h_sum]

  have hd1 : d = 21 := by 
    have eq4 : 3 * d + a + b + c = 87 := by 
      linarith [h4, h_sum]
    linarith [eq4, h_sum]

  rw [ha1, hb1, hc1, hd1]
  norm_num [max_eq_left_of_lt, max_eq_right_of_lt]