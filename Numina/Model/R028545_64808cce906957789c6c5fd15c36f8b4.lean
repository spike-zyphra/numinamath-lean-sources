import Mathlib

theorem algebra_174614 (d a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : d / a = 2 * b) (h' : d / b = 3 * a) :
    b > a := by
  have h1 : d = 2 * a * b := by
    have ha1 : 0 < a := ha
    have eq1 : d / a = 2 * b := h
    have : d = a * (d / a) := by
      field_simp [show a ≠ 0 by linarith]
      <;> nlinarith
    rw [eq1] at this
    linarith
  have h2 : d = 3 * a * b := by
    have hb1 : 0 < b := hb
    have eq2 : d / b = 3 * a := h'
    have : d = b * (d / b) := by
      field_simp [show b ≠ 0 by linarith]
      <;> nlinarith
    rw [eq2] at this
    linarith
  have h3 : 2 * a * b = 3 * a * b := by
    linarith [h1, h2]
  have h4 : a * b = 0 := by 
    nlinarith
  have h7 : a * b > 0 := by 
    positivity
  nlinarith