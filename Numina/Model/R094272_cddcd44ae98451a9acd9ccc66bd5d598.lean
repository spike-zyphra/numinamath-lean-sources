import Mathlib

theorem algebra_314525 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n) (h : ∀ n, ∑ i in Finset.Icc 1 n, a i / ∑ i in Finset.Icc 1 n, b i = (3 * n + 31) / (31 * n + 3)) :
    b 28 / a 28 = 1 ∧ {n | 0 < n ∧ ∃ k : ℤ, b n / a n = k} = {1, 18, 35, 154} := by
  have h0 := h 0
  norm_num [Finset.sum_eq_zero] at h0 
  all_goals linarith