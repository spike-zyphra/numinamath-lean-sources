import Mathlib

theorem algebra_303 (x : ℝ) (hx : x ≠ 0) (hx2 : x ≠ 7) (hx3 : x ≠ -1/2) : (13*x+14)/(2*x^3-13*x^2-7*x) = -(2/x) + (1/(x-7)) + (2/(2*x+1)) := by
  have h1 : 2 * x ^ 3 - 13 * x ^ 2 - 7 * x = x * (2 * x + 1) * (x - 7) := by
    ring
  rw [h1]
  have hx4 : x ≠ 0 := hx
  have hx5 : x - 7 ≠ 0 := by
    intro h
    apply hx2
    linarith
  have hx6 : 2 * x + 1 ≠ 0 := by
    intro h
    have : x = -1 / 2 := by
      linarith
    contradiction
  field_simp [(show x ≠ 0 by exact hx), (show x - 7 ≠ 0 by intro h; apply hx2; linarith), (show (2 * x + 1) ≠ 0 by intro h; apply hx3; linarith)]
  ring