import Mathlib

/-
Find $x+y$, given that $x^{2}-y^{2}=10$ and $x-y=2$.
-/
theorem algebra_610866 (x:ℝ) (y: ℝ) (hminus: x-y = 2)
  (hminux_sq: x^2-y^2 = 10):  x + y = 5 := by
  -- Use identity (x+y)(x-y) = x^2-y^2
  have h1: x^2-y^2 = (x+y)*(x-y) := by
    ring
  rw [hminus] at h1
  rw [hminux_sq] at h1
  linarith