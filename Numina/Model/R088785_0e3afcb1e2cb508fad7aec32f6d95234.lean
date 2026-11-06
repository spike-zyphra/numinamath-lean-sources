import Mathlib

open Real

theorem inequalities_256268 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    (1 - x) * (1 - x) ≤ 1 - 2 * x + x * x := by 
  have h1 : (1 - x) * (1 - x) = 1 - 2 * x + x * x := by
    ring
  rw [h1]
  all_goals try { linarith }