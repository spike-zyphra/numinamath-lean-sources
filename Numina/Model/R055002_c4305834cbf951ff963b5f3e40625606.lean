import Mathlib

theorem algebra_5932 {a b : ℤ} (ha : a + b = 9) (hb : a ^ 2 + b ^ 2 = 45) (h : b > a) :
    b / a = 2 := by 
  have h1 : a * b = 18 := by 
    have h2 : a ^ 2 + b ^ 2 = 45 := hb 
    have h3 : a + b = 9 := ha 
    have h4 : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by 
      ring 
    rw [h3] at h4 
    linarith [h2, h4] 
  have hb_eq : b = 9 - a := by linarith 
  rw [hb_eq] at h1 
  have h6 : a ^ 2 - 9 * a + 18 = 0 := by 
    nlinarith 
  have factored : (a - 6) * (a - 3) = 0 := by 
    nlinarith [h6] 
  cases' (mul_eq_zero.mp factored) with ha6 ha3 
  · -- Case $a = 6$
    have ha6' : a = 6 := by linarith 
    have hb3' : b = 3 := by 
      linarith [ha6', ha] 
    linarith [hb3', ha6', h] 
  · -- Case $a = 3$
    have ha3' : a = 3 := by linarith 
    have hb6' : b = 6 := by 
      linarith [ha3', ha] 
    have : b / a = 2 := by 
      rw [hb6', ha3'] 
      norm_num 
    exact this