import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_273060 {u : ℕ → ℝ}
  (hu1 : u 1 = 1)
  (hun : ∀ n, u (n + 1) = (∑ k in range n, u (k + 1)) ^ (-1 : ℤ)) :
  ∃ α β, Tendsto (λ n => (∑ k in range n, u (k + 1)) / (α * n ^ β)) atTop (𝓝 1) := by
  have h1 := hun 0
  norm_num [Finset.sum_range_zero] at h1 hu1
  all_goals
    linarith