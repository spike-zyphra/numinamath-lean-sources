import Mathlib

theorem calculus_11451 (a b : ℝ) (ha : Real.sin (a + b) = 3 / 4) (hb : Real.sin (a - b) = 1 / 2) :
    Real.tan a / Real.tan b = 5 := by
  have h1 : Real.sin a * Real.cos b + Real.cos a * Real.sin b = 3 / 4 := by
    rw [Real.sin_add] at ha
    linarith
  have h2 : Real.sin a * Real.cos b - Real.cos a * Real.sin b = 1 / 2 := by
    rw [Real.sin_sub] at hb
    linarith
  have h3 : Real.sin a * Real.cos b = 5 / 8 := by 
    linarith
  have h4 : Real.cos a * Real.sin b = 1 / 8 := by 
    linarith
  have h5 : Real.cos a ≠ 0 := by
    by_contra h
    have h6 : Real.cos a * Real.sin b = 0 := by 
      rw [h]
      ring 
    linarith [h4, h6]
  have h6 : Real.sin b ≠ 0 := by 
    by_contra h
    have h7 : Real.cos a * Real.sin b = 0 := by 
      rw [h]
      ring 
    linarith [h4, h7]
  have h7 : Real.tan a = Real.sin a / Real.cos a := by 
    rw [Real.tan_eq_sin_div_cos]
  have h8 : Real.tan b = Real.sin b / Real.cos b := by 
    rw [Real.tan_eq_sin_div_cos]
  rw [h7, h8]
  field_simp [h5, h6]
  <;> linarith [h3, h4]