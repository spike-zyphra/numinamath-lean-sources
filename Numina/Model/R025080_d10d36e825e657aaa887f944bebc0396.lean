import Mathlib

open Real

theorem calculus_56057 {f : ℝ → ℝ}
    (hf : f = fun x => x^5 / (5 * x^4 - 10 * x^3 + 10 * x^2 - 5 * x + 1)) :
    ∑ i ∈ Finset.range 2009, f ((i + 1) / 2009) = 1005 := by
  rw [hf]
  norm_num [Finset.sum_range_succ]