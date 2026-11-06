import Mathlib

theorem algebra_9435 {f : ℝ → ℝ} (hf : f = fun x => 4 * x ^ 6 + 3 * x ^ 5 + 4 * x ^ 4 + 2 * x ^ 3 + 5 * x ^ 2 - 7 * x + 9) :
    f 4 = 20669 := by
  rw [hf]
  -- Lean's `norm_num` tactic can compute arithmetic expressions directly
  norm_num