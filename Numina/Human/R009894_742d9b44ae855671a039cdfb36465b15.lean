import Mathlib

/-Expand $((2x^2+3x+3)-(x^2+6x-6))(x+3)$.-/
theorem algebra_20057 (x : ℝ) : ((2 * x ^ 2 + 3 * x + 3 - (x ^ 2 + 6 * x - 6)) * (x + 3)) = x ^ 3 + 27 := by
  -- simply do some calculation
  calc
    ((2 * x ^ 2 + 3 * x + 3 - (x ^ 2 + 6 * x - 6)) * (x + 3)) = (x ^ 2 - 3 * x + 9) * (x + 3) := by ring_nf
    _ = x * (x ^ 2 - 3 * x + 9) + 3 * (x ^ 2 - 3 * x + 9) := by ring_nf
    _ = x ^ 3 - 3 * x ^ 2 + 9 * x + 3 * x ^ 2 - 9 * x + 27 := by ring_nf
    _ = x ^ 3 + 27 := by ring_nf