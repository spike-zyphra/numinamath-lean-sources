import Mathlib

theorem algebra_184330 {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    (h : ∀ n, ∑ i in Finset.range (n + 1), a i ^ 3 = (∑ i in Finset.Icc 1 n, a i) ^ 3) :
    ∀ n, a n = n := by

  have h0 := h 0
  norm_num [Finset.sum_range_succ, Finset.sum_eq_zero] at h0
  have h1 : a 0 > 0 := ha 0
  nlinarith [sq_nonneg (a 0), sq_pos_of_pos h1, h0]