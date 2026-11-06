import Mathlib

theorem algebra_307651 {p q : ℝ} (h : ¬∃ x : ℝ, x^2 + 2 * p * x - q = 0) : p + q < 1 / 4 := by 
  have h1 : ∀ x : ℝ, x^2 + 2 * p * x - q ≠ 0 := by
    intro x
    by_contra h_eq
    have h2 : ∃ x : ℝ, x^2 + 2 * p * x - q = 0 := ⟨x, h_eq⟩
    exact h h2
  have h2 : p^2 + q < 0 := by 
    by_contra h_nonneg
    push_neg at h_nonneg
    have h3 : ∃ x : ℝ, x^2 + 2 * p * x - q = 0 := by 
      use -p + Real.sqrt (p^2 + q)
      nlinarith [Real.sqrt_nonneg (p^2 + q), Real.sq_sqrt (show 0 ≤ (p^2 + q) by linarith)]
    exact h h3
  nlinarith [sq_nonneg (p - 1 / 2), h2]