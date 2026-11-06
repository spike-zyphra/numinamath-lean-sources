import Mathlib

theorem algebra_311577 {a : ℕ → ℝ} (ha : ∀ n, a n > 0)
    (h : ∀ n, (Finset.sum (Finset.range n) fun i => a i) * (-1) + 2 * a n + 2 ^ (n + 1) = 0)
    (b : ℕ → ℝ) (hb : ∀ n, b n = (n - 2011) / (n + 1) * a n)
    (n0 : ℕ) (hn0 : ∀ k, 0 < k → b k ≤ b n0) :
    n0 = 2009 ∨ n0 = 2010 := by 
  have h0 := h 0
  norm_num [Finset.sum_range_zero] at h0
  have ha0 := ha 0
  linarith