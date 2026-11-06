import Mathlib

theorem algebra_304128 {a b : ℕ → ℝ} {h : ∃ d1 d2, ∀ n, a n = a 0 + d1 * n ∧ b n = b 0 + d2 * n}
    (h' : ∀ n, ∑ i in Finset.range n, a i / ∑ i in Finset.range n, b i = (5 * n - 3) / (2 * n + 1)) :
    a 20 / b 7 = 64 / 9 := by
  specialize h' 0
  norm_num [Finset.sum_range_zero] at h'