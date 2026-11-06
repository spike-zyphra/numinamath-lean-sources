import Mathlib

theorem algebra_193943 (a : ℕ → ℝ) (h : ∀ x, (x^2 - x - 2)^3 = ∑ i ∈ Finset.range 7, a i * x^i) :
    a 1 + a 3 + a 5 = -4 := by
  have h1 := h 1
  have h2 := h (-1)
  simp [Finset.sum_range_succ, pow_two, pow_succ] at h1 h2
  linarith