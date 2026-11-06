import Mathlib

theorem algebra_218429 (a : ℕ → ℝ) (h : ∀ x, (x^2 + 2 * x - 2)^6 = ∑ i in Finset.range 13, a i * (x + 2)^i) :
    a 0 + a 1 + 2 * a 2 + 3 * a 3 + 4 * a 4 + 5 * a 5 + 6 * a 6 + 7 * a 7 + 8 * a 8 + 9 * a 9 + 10 * a 10 + 11 * a 11 + 12 * a 12 = 64 := by
  have h0 := h (-2)
  have h1 := h (-1)
  have h2 := h 0
  have h3 := h 1
  have h4 := h 2
  have h5 := h 3
  have h6 := h 4
  have h7 := h 5
  have h8 := h 6
  have h9 := h 7
  have h10 := h 8
  have h11 := h 9
  have h12 := h 10
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  linarith