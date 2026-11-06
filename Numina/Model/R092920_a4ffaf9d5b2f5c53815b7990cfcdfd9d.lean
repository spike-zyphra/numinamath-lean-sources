import Mathlib

theorem algebra_305455 (a b c : ℝ) (h₀ : a + b + c > 0) (h₁ : a * b + b * c + c * a > 0) (h₂ : a * b * c > 0) :
    a > 0 ∧ b > 0 ∧ c > 0 := by
  have h3 : a > 0 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (a), sq_nonneg (b - c), sq_nonneg (b + c - a), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos (show 0 < a + b + c by linarith) (show 0 < a + b + c by linarith)]
-- Now Assume b is non-positive and do the tauto.
  have h4 : b > 0 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (b), sq_nonneg (a - c), sq_nonneg (a + c - b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_pos (show 0 < a + b + c by linarith) (show 0 < a + b + c by linarith)]
  have h5 : c > 0 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (b + a - c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_pos (show 0 < a + b + c by linarith) (show 0 < a + b + c by linarith)]
  exact ⟨h3, h4, h5⟩