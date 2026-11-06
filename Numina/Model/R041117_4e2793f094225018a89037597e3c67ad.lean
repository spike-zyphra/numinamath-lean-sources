import Mathlib

theorem algebra_258261 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n) (h : ∀ n, ∑ i in Finset.Icc 1 n, a i / ∑ i in Finset.Icc 1 n, b i = (3 * n + 5) / (5 * n + 3)) :
    a 10 / b 6 = 31 / 29 := by
  have h0 := h 0
  norm_num [Finset.sum_eq_zero] at h0
  all_goals
    linarith