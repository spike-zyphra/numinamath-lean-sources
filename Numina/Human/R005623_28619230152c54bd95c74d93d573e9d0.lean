import Mathlib

/-
Evaluate $2+5+8+\cdots+101$.
-/
theorem algebra_609157 : ∑ x ∈ Finset.range 34, (3 * x + 2) = 1751 := by
  -- expand the sum to $3 \sum_{x=0}^{33} x + 2 \sum_{x=0}^{33} 1$ and simplify
  rw [
    Finset.sum_add_distrib,
    Finset.sum_eq_card_nsmul (show ∀ x ∈ Finset.range 34, 2 = 2 by intro _ _; rfl),
    <-Finset.mul_sum,
    Finset.sum_range_id
  ]
  simp
