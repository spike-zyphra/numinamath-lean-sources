import Mathlib

theorem algebra_278669 (a c : ℝ) (ha : -4 ≤ a * 1^2 - c ∧ a * 1^2 - c ≤ -1)
    (hb : -1 ≤ a * 2^2 - c ∧ a * 2^2 - c ≤ 5) :
    -1 ≤ a * 3^2 - c ∧ a * 3^2 - c ≤ 20 := by 
  constructor
  · -- Show that -1 ≤ a * 3^2 - c
    linarith
  · -- Show that a * 3^2 - c ≤ 20
    linarith