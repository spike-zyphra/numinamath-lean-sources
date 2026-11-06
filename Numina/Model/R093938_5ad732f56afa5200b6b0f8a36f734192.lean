import Mathlib

theorem inequalities_6181 (p : ℝ) (h : p > 0) :
    (10 * 15) * p ≤ 900 ↔ p ≤ 6 := by
  constructor
  · -- Forward direction: If (10 * 15) * p ≤ 900, then p ≤ 6
    intro h1
    linarith
  · -- Backward direction: If p ≤ 6, then (10 * 15) * p ≤ 900
    intro h2
    linarith