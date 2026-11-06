import Mathlib

theorem algebra_598154 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n) (h : ∀ n, (∑ i in Finset.range n, a i) / (∑ i in Finset.range n, b i) = (7 * n + 1) / (n + 3)) :
    (a 2 + a 5 + a 17 + a 22) / (b 8 + b 10 + b 12 + b 16) = 31 / 5 := by

  have h0 := h 0
  norm_num at h0
  all_goals
    linarith