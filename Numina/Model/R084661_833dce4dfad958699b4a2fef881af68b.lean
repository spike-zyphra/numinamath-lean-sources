import Mathlib

theorem algebra_7852 {a : ℕ → ℝ} (h : ∀ x, (2*x^2 - x - 1)^4 = ∑ i in Finset.range 9, a i * x ^ i) :
    a 0 + a 2 + a 4 + a 6 + a 8 - 2*(a 1 + a 3 + a 5 + a 7) = 24 := by 
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  simp [Finset.sum_range_succ] at h0 h1 hm1 h2
  linarith