import Mathlib

theorem algebra_122162 {a b c d x : ℝ} (h : a ≠ c) (ha : a + d = 2016) (hb : b + c = 2016)
    (hroots : (x - a) * (x - b) = (x - c) * (x - d)) : x = 1008 := by 
  have eq1 : x * (c + d - a - b) = (c * d - a * b) := by 
    nlinarith 
  have h_eq : c + d - a - b ≠ 0 := by 
    by_contra h_zero
    have h4 : a + b = 2016 := by 
      nlinarith 
    have ha1 : a = 2016 - d := by linarith [ha]
    have hb1 : b = 2016 - c := by linarith [hb]
    have h_eq1 : a + b = 2016 := by 
      nlinarith 
    have ha_eq : a = 2016 - d := by linarith [ha]
    have hb_eq : b = 2016 - c := by linarith [hb]
    have hc_eq : c = 2016 - d := by 
      nlinarith [hb_eq, ha_eq, h_zero]
    have h_eq1 : a = c := by 
      nlinarith [hb_eq, ha_eq, h_zero]
    contradiction 
  have hx : x = (c * d - a * b) / (c + d - a - b) := by 
    field_simp [h_eq] 
    <;> nlinarith 
  rw [hx]
  have ha1 : a = 2016 - d := by linarith 
  have hb1 : b = 2016 - c := by linarith 
  rw [ha1, hb1] 
  field_simp [show (c + d - (2016 - d) - (2016 - c)) ≠ 0 by 
    by_contra h_zero 
    have h5 : (c + d - (2016 - d) - (2016 - c)) = 0 := by linarith [h_zero]
    have h3 : c + d - a - b = 0 := by 
      nlinarith [h5, ha, hb]
    exfalso 
    exact h_eq (by linarith [h3]) 
 ]
  <;> nlinarith [sq_nonneg (a - c), sq_nonneg (c + d - 2016)]