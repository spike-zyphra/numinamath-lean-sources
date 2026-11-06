import Mathlib

open Set Real

theorem inequalities_12723 {x : ℝ} (hx : (x^2 - 5 * x - 6 < 0) ∧ (abs (x + 2) ≤ 3)) :
    -1 < x ∧ x ≤ 1 := by
  have h1 : x^2 - 5 * x - 6 < 0 := hx.1
  have h2 : abs (x + 2) ≤ 3 := hx.2
  have h3 : -1 < x := by
    nlinarith
  have h4 : x ≤ 1 := by
    rw [abs_le] at h2
    linarith
  constructor
  · linarith
  · linarith