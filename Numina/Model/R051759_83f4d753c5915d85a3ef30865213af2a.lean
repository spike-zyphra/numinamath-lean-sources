import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_155681 {f : ℝ → ℝ} (hf : f = λ x => arctan (5 * x) + x ^ 2) :
    deriv f (1 / 5) = 2.9 := by
  rw [hf]
  simp [deriv_add, deriv_pow, deriv_mul, deriv_id'', mul_comm]
  all_goals norm_num