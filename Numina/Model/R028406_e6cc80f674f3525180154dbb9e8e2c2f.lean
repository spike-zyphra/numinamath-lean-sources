import Mathlib

set_option maxRecDepth 100000000

theorem algebra_13001 (x : ℤ) : ∑ i ∈ Finset.range 1987, (i + 1) * (1987 - (i : ℝ)) = 1987 * 994 * x ↔ x = 663 := by
  constructor
  · -- Forward: if the equation holds, then x = 663
    intro h
    norm_num [Finset.sum_range_succ] at h
    have h1 : (x : ℝ) = 663 := by
      linarith
    have h2 : x = 663 := by
      exact_mod_cast h1
    exact h2
  · -- Backward: if x = 663, then the equation holds
    intro h
    rw [h]
    norm_num [Finset.sum_range_succ]