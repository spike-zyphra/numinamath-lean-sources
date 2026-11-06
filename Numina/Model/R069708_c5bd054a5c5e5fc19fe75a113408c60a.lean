import Mathlib

theorem algebra_320469 {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (hsum : ∀ n, a n ^ 2 + a n - 2 * ∑ i in Finset.range n, a i = 0) :
    (∀ n, a n = 4 - (2 * n + 4) * (1 / 2) ^ n) ∧
    (∃ m M, ∀ n, 0 < n → m < ∑ i in Finset.range n, a i * (1 / 2) ^ i ∧
      ∑ i in Finset.range n, a i * (1 / 2) ^ i < M ∧ M - m = 4) := by
  have h1 := hsum 0
  norm_num [Finset.sum_range_zero] at h1
  have h2 : 0 < a 0 := ha 0
  nlinarith