import Mathlib
/- Compute

$$
1 \cdot 2^{2}+2 \cdot 3^{2}+3 \cdot 4^{2}+\cdots+19 \cdot 20^{2}
$$ -/
theorem algebra_608511 : ∑ i in Finset.range 19, (i + 1) * (i + 2) ^ 2 = 41230:= by
  -- Use simp tactic with Finset.sum_range_succ to simplify the sum
  simp [Finset.sum_range_succ]
