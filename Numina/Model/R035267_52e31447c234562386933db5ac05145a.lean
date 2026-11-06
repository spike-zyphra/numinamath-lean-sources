import Mathlib

theorem inequalities_115803 (x y : ℕ) (h : x^2 + 1 < y^2 ∧ y^2 < x^2 + x + 1) :
    False := by
  have h1 : x ^ 2 + 1 < y ^ 2 := h.1
  have h2 : y ^ 2 < x ^ 2 + x + 1 := h.2
  have h3 : x < y := by
    by_contra h4
    push_neg at h4
    have h5 : y ≤ x := by linarith
    have h6 : y ^ 2 ≤ x ^ 2 := by nlinarith
    nlinarith
  have h4 : y < x + 1 := by
    by_contra h4
    push_neg at h4
    have h6 : y ≥ x + 1 := by
      omega
    have h7 : y ^ 2 ≥ (x + 1) ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg (y - (x + 1) : ℕ), sq_nonneg (x : ℕ), sq_nonneg (y : ℕ)]
  omega