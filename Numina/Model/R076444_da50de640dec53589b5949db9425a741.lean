import Mathlib

theorem algebra_16475 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a^3 + b^3 = a + b) :
    a / b + b / a - 1 / (a * b) = 1 := by
  have h1 : a + b > 0 := add_pos ha hb
  have h2 : a^3 + b^3 = (a + b) * (a^2 - a * b + b^2) := by 
    ring
  rw [h2] at h
  have h3 : a^2 - a * b + b^2 = 1 := by 
    apply (mul_left_inj' (show (a + b) ≠ 0 by linarith [h1])).mp 
    linarith
  have h4 : a^2 + b^2 = 1 + a * b := by
    nlinarith [h3]
  have ha' : a ≠ 0 := by linarith
  have hb' : b ≠ 0 := by linarith
  field_simp [ha', hb']
  nlinarith [h4]