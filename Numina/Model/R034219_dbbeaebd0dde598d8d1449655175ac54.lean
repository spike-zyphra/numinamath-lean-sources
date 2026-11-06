import Mathlib

theorem algebra_8462 {a b c : ℤ} (ha : a < b) (hb : b < c) (h1 : a + b + c = 95) (h2 : a^2 + b^2 + c^2 = 3083) :
    c = 37 := by
  have h3 : c = 95 - a - b := by linarith
  rw [h3] at h2
  have h4 : a ≤ 93 := by nlinarith
  have h5 : a ≥ 1 := by nlinarith
  have h6 : b ≤ 94 := by nlinarith
  have h7 : b ≥ 2 := by nlinarith
  -- Completing the squares.
  interval_cases a <;> interval_cases b <;> omega