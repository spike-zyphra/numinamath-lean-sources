import Mathlib

theorem algebra_597319 (a b c : ℝ) (h₀ : a + b + c > 0) (h₁ : a * b + b * c + c * a > 0) (h₂ : a * b * c > 0) :
    a > 0 ∧ b > 0 ∧ c > 0 := by
  have ha : a > 0 := by
    by_contra h
    push_neg at h
    have h3 : a * b * c > 0 := h₂
    have h4 : b * c < 0 := by 
      nlinarith [sq_nonneg (a), sq_nonneg (b * c), sq_nonneg (a * (b * c)), h, h3, mul_nonpos_of_nonpos_of_nonneg (show a ≤ 0 by linarith) (show 0 ≤ (0 : ℝ) by linarith)]
    nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), mul_self_nonneg (a - b), mul_self_nonneg (a - c), mul_self_nonneg (b - c)]
  have hb : b > 0 := by
    by_contra h
    push_neg at h
    -- Contradiction
    nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), mul_self_nonneg (a - b), mul_self_nonneg (a - c), mul_self_nonneg (b - c)]
  have hc : c > 0 := by 
    nlinarith [ha, hb, h₀, h₁, h₂, mul_pos ha hb, mul_pos hb (show 0 < a by linarith [ha])]
  exact ⟨ha, hb, hc⟩