import Mathlib

theorem algebra_277278 {a : ℕ → ℝ} (ha : ∃ i, a i ≠ 0)
    (h : ∀ i, a (i + 1) ^ 2 - a i * a (i + 1) + a i ^ 2 = 0)
    (h' : ∀ i, a (i + 1) ≠ a (i - 1)) (ha1 : a 1 = 1) (ha2 : a (n + 1) = 1)
    (n : ℕ) :
    ∑ i in Finset.range n, a i = 0 := by
  have h0 := h 0
  rw [ha1] at h0
  nlinarith [sq_nonneg (a 0 - 0.5), sq_nonneg (a 0 - 1)]