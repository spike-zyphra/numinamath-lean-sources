import Mathlib

/- Let $x$ be a real number such that $x^{3}+4 x=8$. Determine the value of $x^{7}+64 x^{2}$.-/
theorem algebra_611198 (x : ℝ) (hx : x ^ 3 + 4 * x = 8) : x ^ 7 + 64 * x ^ 2 = 128 := by
  -- We have: 
  -- x ^ 7 + 4 * x ^ 5 = 8 * x ^ 4
  -- -4 * x ^ 5 - 16 * x ^ 3 = -32 * x ^ 2
  -- 8 * x ^ 4 - 32 * x ^ 2 = 64 * x
  -- 16 * x ^ 3 + 64 * x = 128
  -- Multiply both sides of hx by (x⁴ - 4x² + 8x + 16), which is the same as adding the four equations above.
  have hx1 := congr_arg (· * (x ^ 4 - 4 * x ^ 2 + 8 * x + 16)) hx
  ring_nf at hx1
  linarith

