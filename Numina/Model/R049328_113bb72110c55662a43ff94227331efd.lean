import Mathlib

theorem algebra_325602 {x : ℕ → ℝ} (hx : ∀ i, x i = i / 101) :
    ∑ i in Finset.range 102, (x i)^3 / (3 * (x i)^2 - 3 * x i + 1) = 51 := by 
  norm_num [Finset.sum_range_succ, hx]
  <;> ring_nf 
  <;> norm_num