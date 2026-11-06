import Mathlib

theorem algebra_299764 {a b : ℝ} (ha : a ≠ -1) (hb : b ≠ 1)
    (h : a + 1 / (a + 1) = b + 1 / (b - 1) - 2) (h' : a - b + 2 ≠ 0) :
    a * b - a + b = 2 := by
  have eq1 : a + 1 ≠ 0 := by
    intro h1
    apply ha
    linarith

  have eq2 : b - 1 ≠ 0 := by
    intro h1
    apply hb
    linarith

  field_simp [eq1, eq2] at h 
  ring_nf at h 
  nlinarith [h, sq_pos_of_ne_zero (show (a - b + 2) ≠ 0 by exact h')]