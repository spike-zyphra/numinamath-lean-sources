import Mathlib

theorem algebra_1068 (a b c : ℝ) (h₀ : a * b > 1) (h₁ : b * c > 1) (h₂ : c * a > 1) :
    (a * b * c) ^ 2015 > 1 ∨ (a * b * c) ^ 2015 < -1 := by

  have h3 : (a * b * c) ^ 2 > 1 := by
    have h3a : (a * b * c) ^ 2 = (a * b) * (b * c) * (c * a) := by
      ring
    rw [h3a]
    have h7 : (a * b) * (b * c) * (c * a) > 1 := by
      have h4 : (a * b) > 1 := h₀
      have h5 : (b * c) > 1 := h₁
      have h6 : (c * a) > 1 := h₂
      have h7 : (a * b) * (b * c) > 1 := by
        nlinarith [mul_pos (show (0 : ℝ) < (a * b - 1) by nlinarith) (show (0 : ℝ) < (b * c - 1) by nlinarith)]
      have h8 : (a * b) * (b * c) * (c * a) > 1 := by
        nlinarith [mul_pos (show (0 : ℝ) < (a * b * (b * c) - 1) by nlinarith) (show (0 : ℝ) < (c * a - 1) by nlinarith)]
      linarith
    nlinarith

  have h5 : (a * b * c) > 1 ∨ (a * b * c) < -1 := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (a * b * c), h]

  rcases h5 with h5 | h5
  · -- If a*b*c > 1, then $A = (a*b*c)^{2015} > 1$.
    left
    have h6 : (a * b * c) ^ 2015 > 1 := by
      have h7 : (a * b * c) > 1 := h5
      have h8 : (a * b * c) ^ 2015 > (1 : ℝ) := by
        apply one_lt_pow
        all_goals
          nlinarith
      linarith
    linarith
  · -- If a*b*c < -1, then $A = (a*b*c)^{2015} < -1$.
    right
    have h6 : (a * b * c) ^ 2015 < -1 := by
      have h7 : (a * b * c) < -1 := h5
      have h11 : (a * b * c) ^ 2015 < (-1 : ℝ) := by
        have h15 : - (a * b * c) > 1 := by nlinarith
        have h16 : (- (a * b * c)) ^ 2015 > (1 : ℝ) := by
          apply one_lt_pow
          all_goals
            nlinarith
        have h17 : (a * b * c) ^ 2015 = - ((- (a * b * c)) ^ 2015) := by
          ring
        nlinarith
      linarith
    linarith