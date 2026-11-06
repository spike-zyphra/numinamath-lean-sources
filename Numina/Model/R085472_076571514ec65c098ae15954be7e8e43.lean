import Mathlib

theorem algebra_273354 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 1 / (a + b) = 12) (h2 : a * 3 + b * 8 = 5 / 12) :
    1 / a = 20 := by
  have eq1 : a + b = 1 / 12 := by 
    have h12 : a + b ≠ 0 := by 
      linarith [show a > 0 by linarith, show b > 0 by linarith]
    field_simp at h1 
    linarith 
  have eq2 : b = 1 / 12 - a := by 
    linarith [eq1] 
  rw [show b = 1 / 12 - a by linarith [eq1]] at h2 
  have ha_eq : a = 1 / 20 := by
    linarith 
  have ha20 : 1 / a = 20 := by 
    rw [ha_eq] 
    field_simp 
  exact ha20