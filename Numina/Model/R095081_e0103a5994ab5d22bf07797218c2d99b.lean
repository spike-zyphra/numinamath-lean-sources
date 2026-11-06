import Mathlib

theorem algebra_285650 (d a b : ℝ) (ha : a > 0) (hb : b > 0)
    (h : d / a = 12) (h' : d / b = 100 / 65) (h'' : d / a + d / b = 20) :
    d = 1700 := by
  have ha' : a ≠ 0 := by linarith
  have hb' : b ≠ 0 := by linarith

  have h1 : d = 12 * a := by
      field_simp [ha'] at h 
      linarith
  have h2 : d = (100 / 65) * b := by
      field_simp [hb'] at h'
      linarith
  have h3 : d / a + d / b = 20 := by linarith
  
  field_simp [ha', hb'] at h3
  nlinarith