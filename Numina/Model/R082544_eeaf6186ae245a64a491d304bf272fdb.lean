import Mathlib
open Real

theorem algebra_9678 {f : ℝ → ℝ} (hf : f = λ x => (x^2 - 2 * x + 3) / (x - 1)) :
    ∑ i ∈ Finset.range 22, ⌊f (i + 2)⌋ = 256 := by
  norm_num [Finset.sum_range_succ, hf, Int.floor_eq_iff]