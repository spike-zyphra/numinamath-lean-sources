import Mathlib

theorem algebra_677 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) 
    (h1 : 1 / (b - a) = 30) 
    (h2 : 1 / (2 * b - a) = 10) :
    1 / (3 * b) = 5 := by
  have h3 : b - a ≠ 0 := by
    intro h
    rw [h] at h1
    linarith
  have h4 : 2 * b - a ≠ 0 := by
    intro h
    rw [h] at h2
    linarith
  field_simp at *
  linarith