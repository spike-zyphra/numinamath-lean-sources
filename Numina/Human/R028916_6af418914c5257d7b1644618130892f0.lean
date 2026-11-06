import Mathlib

theorem algebra_154499 {a b : ℝ} (ha : a ≠ -1) (hb : b ≠ -1) (h : a / (1 + b) + b / (1 + a) = 1) :
    a^3 + b^3 = a + b := by
  have h1 : (1 + b) ≠ 0 := by
    intro h2
    have : b = -1 := by linarith
    contradiction
  have h2 : (1 + a) ≠ 0 := by
    intro h3
    have : a = -1 := by linarith
    contradiction
  field_simp [(show 1 + b ≠ 0 by assumption), (show 1 + a ≠ 0 by assumption)] at h
  ring_nf at h
  have h3 : a^2 + b^2 = 1 + a * b := by linarith
  have h4 : a^2 - a * b + b^2 = 1 := by linarith
  have h5 : a^3 + b^3 = (a + b) * (a^2 - a * b + b^2) := by ring
  rw [h5, h4]
  ring