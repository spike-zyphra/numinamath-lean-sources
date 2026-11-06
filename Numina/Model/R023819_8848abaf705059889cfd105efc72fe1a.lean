import Mathlib

theorem algebra_320934 (m : ℝ) (h : ∃! x : ℝ, x ≥ 2 ∧ x^4 + (m - 4) * x^2 + 2 * (1 - m) = 0) :
    m ≤ -1 := by 
  rcases h with ⟨x, ⟨hx1, hx2⟩, h2⟩
  by_contra h3
  push_neg at h3
  have eqn : x^4 + (m - 4) * x^2 + 2 * (1 - m) = 0 := hx2
  have h4 : x ≥ 2 := hx1
  by_cases h5 : x > 2
  · -- When x > 2
    have hx2m : m < -1 := by
      nlinarith [sq_nonneg (x^2 - 2), sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (m), sq_pos_of_pos (show (0 : ℝ) < x - 2 by linarith)]
    linarith
  · -- When x = 2
    have h9 : x = 2 := by linarith
    have h10 : m = -1 := by
      rw [show x = (2 : ℝ) by linarith] at eqn
      nlinarith
    linarith