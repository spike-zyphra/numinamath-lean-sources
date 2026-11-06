import Mathlib

theorem inequalities_39645 (a b c : ℝ) (h₀ : b * c ≠ 0) (h₁ : (1 - c ^ 2) / (b * c) ≥ 0) : 10 * (a ^ 2 + b ^ 2 + c ^ 2 - b * c ^ 3) ≥ 2 * a * b + 5 * a * c := by
  by_cases h2 : b * c > 0
  · -- Case where b * c > 0. Then 1 - c^2 ≥ 0.
    have h3 : (1 - c ^ 2) / (b * c) ≥ 0 := h₁
    have h4 : 1 - c ^ 2 ≥ 0 := by
      have h₃ : b * c > 0 := h2
      have h₄ : (1 - c ^ 2) / (b * c) ≥ 0 := h₁
      apply div_nonneg_iff.mp at h₄
      cases h₄ with
      | inl h₅ =>
        nlinarith
      | inr h₆ =>
        nlinarith
    have h5 : c ^ 2 ≤ 1 := by linarith
    nlinarith [sq_nonneg (a - b / 2 - c * 5 / 20), sq_nonneg (c - 1 / 2), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (b - a / 2), sq_nonneg (c - 1), sq_nonneg (c + 1), sq_nonneg (b * c), sq_nonneg ((c ^ 2 - 1)), sq_nonneg (c), sq_nonneg (b)]
  · -- Case where b * c ≤ 0. Then 1 - c^2 ≤ 0.
    have h3 : b * c ≤ 0 := by
      by_contra h6
      push_neg at h6
      have : b * c > 0 := by nlinarith
      contradiction
    have h4 : b * c < 0 := by
      by_contra h7
      push_neg at h7
      have : b * c = 0 := by
        have : b * c ≤ 0 := by linarith
        have : b * c ≥ 0 := by
          nlinarith
        nlinarith
      contradiction
    have h5 : (1 - c ^ 2) / (b * c) ≥ 0 := h₁
    have h8 : 1 - c ^ 2 ≤ 0 := by
      have h₃ : b * c < 0 := h4
      have h₄ : (1 - c ^ 2) / (b * c) ≥ 0 := h₁
      apply div_nonneg_iff.mp at h₄
      cases h₄ with
      | inl h₅ =>
        nlinarith
      | inr h₆ =>
        nlinarith
    have h9 : c ^ 2 ≥ 1 := by linarith
    nlinarith [sq_nonneg (a - b / 2 - c * 5 / 20), sq_nonneg (c - 1 / 2), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (b - a / 2), sq_nonneg (c - 1), sq_nonneg (c + 1), sq_nonneg (b * c), sq_nonneg ((c ^ 2 - 1)), sq_nonneg (c), sq_nonneg (b)]