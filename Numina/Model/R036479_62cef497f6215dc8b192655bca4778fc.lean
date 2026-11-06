import Mathlib

theorem algebra_22181 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : 1 / a + 1 / b + 1 / c = 0) :
    b * c / a ^ 2 + a * c / b ^ 2 + a * b / c ^ 2 = 3 := by
  have h1 : a * b + a * c + b * c = 0 := by
    field_simp at h
    nlinarith
  have h2 : b * c / a ^ 2 + a * c / b ^ 2 + a * b / c ^ 2 = ( (a * b) ^ 3 + (a * c) ^ 3 + (b * c) ^ 3 ) / ( (a * b * c) ^ 2 ) := by
    field_simp
    ring
  have h3 : (a * b) ^ 3 + (a * c) ^ 3 + (b * c) ^ 3 = 3 * (a * b * (a * c) * (b * c)) := by
    have h4 : a * b + a * c + b * c = 0 := h1
    have h5 : (a * b) + (a * c) + (b * c) = 0 := h1
    have h6 : (a * b) ^ 3 + (a * c) ^ 3 + (b * c) ^ 3 - 3 * (a * b * (a * c) * (b * c)) = 
            ((a * b) + (a * c) + (b * c)) * ((a * b) ^ 2 + (a * c) ^ 2 + (b * c) ^ 2 - (a * b) * (a * c) - (a * b) * (b * c) - (a * c) * (b * c)) := by ring
    rw [show (a * b) + (a * c) + (b * c) = (0 : ℝ) by linarith] at h6
    linarith
  rw [h2] at *
  rw [h3]
  field_simp
  <;> nlinarith