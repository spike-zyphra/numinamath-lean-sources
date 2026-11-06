import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_144373 :
  IsLeast {f | ∃ x y : ℝ, x ≥ 1 / 2 ∧ y ≥ 1 / 2 ∧
    f = x ^ 3 + y ^ 3 + x ^ 2 * y + x * y ^ 2 - 3 * (x ^ 2 + y ^ 2 + x * y) + 3 * (x + y)} 1 := by
  constructor
  · -- Show that 1 is achievable by selecting x = 1 and y = 1
    use 1, 1
    norm_num 
  · -- Show that 1 is the minimum
    intro f hf
    rcases hf with ⟨x, y, hx, hy, hf⟩
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y), 
      sq_nonneg (x + y - 2), 
      mul_nonneg (show (0 : ℝ) ≤ x - 1 / 2 by linarith) (show (0 : ℝ) ≤ y - 1 / 2 by linarith)
    ]