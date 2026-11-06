import Mathlib

theorem inequalities_168736 {a b : ℝ} (ha : 2 ≤ a) (hb : 2 < b) :
    a * b > a + b := by
  have ha1 : 1 ≤ a - 1 := by linarith
  have hb1 : 1 < b - 1 := by linarith
  have h1 : (a - 1) * (b - 1) > 1 := by
    nlinarith
  nlinarith