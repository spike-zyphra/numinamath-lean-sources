import Mathlib

theorem algebra_8414 {f : ℝ → ℝ} (hf : ∀ x y, (x + y) * (f x - f y) = (x - y) * (f x + f y)) :
    ∃ c, ∀ x, f x = c * x := by
  have h1 : f 0 = 0 := by
    specialize hf 1 0
    simp at hf
    linarith
  use f 1
  intro x
  have eq1 := hf x 1
  ring_nf at eq1
  -- Left side: x * f x + f x - x * f 1 - f 1
  -- Right side: x * f x - f x + x * f 1 - f 1
  -- Simplify:
  -- Left side - Right side = f x - x * f 1 - f 1 - (-f x + x * f 1 - f 1) = f x - x * f 1 - f 1 + f x - x * f 1 + f 1 = 2 f x - 2 x * f 1 = 0
  -- => 2 f x = 2 x * f 1 => f x = x * f 1
  have eq2 : f x = f 1 * x := by
    linarith
  linarith