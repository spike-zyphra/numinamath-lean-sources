import Mathlib

theorem algebra_160181 {a : ℕ → ℝ} (h : ∀ x : ℝ, x^5 + 3 * x^3 + 1 = ∑ i in Finset.range 6, a i * (x - 1)^i) :
    a 3 = 13 := by 
  have h0 := h 1
  have h1 := h 2
  have h2 := h 3
  have h3 := h 4
  have h4 := h 5
  have h5 := h 6
  simp [Finset.sum_range_succ] at h0 h1 h2 h3 h4 h5
  linarith