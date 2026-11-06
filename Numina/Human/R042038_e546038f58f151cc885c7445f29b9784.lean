import Mathlib

/-If $3+\sqrt{5}$ is a root of the equation \[x^2 - 3x + b = 0,\]compute $b.$-/
theorem algebra_20401 {b : ℝ} (h : (3 + Real.sqrt 5)^2 - 3 * (3 + Real.sqrt 5) + b = 0) :
    b = -3 * Real.sqrt 5 - 5 := by
  -- simplify the expression h
  ring_nf at h
  rw [Real.sq_sqrt] at h
  linarith only [h]
  norm_num