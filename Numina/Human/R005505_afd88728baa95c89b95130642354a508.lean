import Mathlib
/- Evaluate the sum:

$$
11^{2}-1^{2}+12^{2}-2^{2}+13^{2}-3^{2}+\ldots+20^{2}-10^{2}
$$ -/
theorem algebra_608560 : ∑ i in Finset.range 10, ((i + 11) ^ 2 - (i + 1) ^ 2) = 2100:= by
  -- Expand the square terms
  simp [Finset.sum_range_succ]
