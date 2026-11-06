import Mathlib

open Real Filter Function
open scoped Topology

theorem algebra_6495
  (x : ℕ → ℝ)
  (hx1 : x 1 ∈ Set.Ioo 0 1)
  (hxn : ∀ n, x (n + 1) = (∑ k in Finset.Icc 1 n, log (1 + x k)) / n) :
  Tendsto (λ n => x n * log n) atTop (𝓝 2) := by
  have h0 := hxn 0
  norm_num [Finset.sum_eq_zero] at h0 ⊢
  norm_num [Set.mem_Ioo] at hx1
  all_goals
    linarith