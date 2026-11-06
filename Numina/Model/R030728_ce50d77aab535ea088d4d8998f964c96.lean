import Mathlib

theorem number_theory_208577 : ∑ n in Finset.range 503, ⌊(305 * n : ℝ) / 503⌋ = 76304 := by
  norm_num [Finset.sum_range_succ, Int.floor_eq_iff]
  <;> native_decide