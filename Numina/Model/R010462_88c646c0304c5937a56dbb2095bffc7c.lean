import Mathlib

  theorem algebra_2306 {x y z : ℝ} (h : (x + y) / 11 = (x - y + z) / 5) (h' : (x - y + z) / 5 = (x + y - z) / 7) : x / 6 = y / 5 ∧ y / 5 = z / 4 := by
  have h1 : 5 * (x + y) = 11 * (x - y + z) := by
    linarith
  have h2 : 7 * (x - y + z) = 5 * (x + y - z) := by
    linarith
  constructor
  · -- Show that x / 6 = y / 5
    nlinarith
  · -- Show that y / 5 = z / 4
    nlinarith