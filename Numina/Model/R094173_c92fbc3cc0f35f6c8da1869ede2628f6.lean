import Mathlib

theorem number_theory_281763 : ∑ n in Finset.range 503, ⌊(305 * n / 503 : ℝ)⌋ = 76304 := by 
  norm_num [Finset.sum_range_succ, Int.floor_eq_iff]