import Mathlib

open Complex Finset

/-Simplify: $i^{0}+i^{1}+\cdots+i^{2009}$.-/
theorem algebra_608514 : ∑ l ∈ range 2010, I^l = 1 + I := by
-- Use geom_sum_eq to rewrite the sum, then simplify it to the final goal
  rw [geom_sum_eq, div_eq_iff, add_comm, ← sq_sub_sq, I_sq]
  rw [show 2010 = 2 * 1005 by simp, pow_mul, I_sq, Odd.neg_one_pow]; simp
  use 502; simp; rw [sub_ne_zero]
  all_goals intro h; apply_fun fun t => t.re at h; simp at h