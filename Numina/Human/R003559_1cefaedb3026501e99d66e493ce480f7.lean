import Mathlib

theorem algebra_195849 {x y : ℝ} (hx : x ≠ 0) (h : 10 * x = x + y) :
    x / y = 1 / 9 := by
  have hy : y ≠ 0 := by
    intro h0
    have : x = 0 := by linarith
    contradiction
  have h1 : y = 9 * x := by linarith
  rw [h1]
  field_simp [hx]
  ring