import Mathlib


open Real


theorem algebra_241107 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (h : ∀ n, ∑ i in Finset.range n, a i = n ^ 2 + 1) (ha1 : a 0 > 0)
    (hak : ∀ k ≥ 2, a k = 2 / (k - 1) * ∑ i in Finset.range k, a i) :
    ∀ n, a n = a 0 + d * n := by
  have h0 := h 0
  norm_num [Finset.sum_range_succ] at h0