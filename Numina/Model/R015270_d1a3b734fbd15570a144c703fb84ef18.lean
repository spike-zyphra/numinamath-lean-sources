import Mathlib


theorem algebra_218603 (x : ℝ) :
    (x^4 + x + 1) / (x^4 + x^2 - x - 4) = (x^4 + 1) / (x^4 + x^2 - 4) ↔
    x = -1 ∨ x = 0 ∨ x = 1 := by
  constructor
  · -- Forward implication: if the equation holds, then x ∈ {-1, 0, 1}
    intro h_eq
    have h1 : x^4 + x^2 - x - 4 ≠ 0 := by
      by_contra h
      have h_eq1 : (x^4 + x + 1) / (x^4 + x^2 - x - 4) = 0 := by
        rw [h]
        norm_num
      have h_eq2 : (x^4 + 1) / (x^4 + x^2 - 4) = 0 := by
        linarith [h_eq, h_eq1]
      have h2 : x^4 + 1 = 0 := by
        have h3 : x^4 + x^2 - 4 ≠ 0 := by
          nlinarith [sq_nonneg (x^2), sq_nonneg (x^2 - 2), sq_nonneg (x^2 - 1), sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x - 1)]
        field_simp [h3] at h_eq2 ⊢
        all_goals nlinarith
      nlinarith [sq_nonneg (x^2), sq_nonneg (x^2 - 2), sq_nonneg (x^2 - 1), sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x - 1)]
    have h2 : x^4 + x^2 - 4 ≠ 0 := by
      by_contra h
      have h_eq2 : (x^4 + 1) / (x^4 + x^2 - 4) = 0 := by
        rw [h]
        norm_num
      have h_eq1 : (x^4 + x + 1) / (x^4 + x^2 - x - 4) = 0 := by
        linarith [h_eq, h_eq2]
      have h3 : x^4 + x + 1 = 0 := by
        have h4 : x^4 + x^2 - x - 4 ≠ 0 := by
          nlinarith [sq_nonneg (x^2), sq_nonneg (x^2 - 2), sq_nonneg (x^2 - 1), sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x - 1)]
        field_simp [h4] at h_eq1 ⊢
        all_goals nlinarith
      nlinarith [sq_nonneg (x^2), sq_nonneg (x^2 - 2), sq_nonneg (x^2 - 1), sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x - 1)]
    have h3 : (x^4 + x + 1) * (x^4 + x^2 - 4) = (x^4 + 1) * (x^4 + x^2 - x - 4) := by
      have h4 : (x^4 + x + 1) / (x^4 + x^2 - x - 4) = (x^4 + 1) / (x^4 + x^2 - 4) := h_eq
      have h5 : (x^4 + x + 1) * (x^4 + x^2 - 4) = (x^4 + 1) * (x^4 + x^2 - x - 4) := by
        field_simp [h1, h2] at h4 ⊢
        all_goals nlinarith
      linarith
    have h4 : 2 * x^5 + x^3 - 3 * x = 0 := by
      nlinarith
    have h5 : x * (2 * x^4 + x^2 - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- x = 0
      right
      left
      linarith
    · -- 2 * x^4 + x^2 - 3 = 0
      have h8 : 2 * (x^2)^2 + x^2 - 3 = 0 := by
        nlinarith
      have h9 : (x^2 - 1) * (2 * x^2 + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- x^2 - 1 = 0
        have h12 : x^2 = 1 := by
          linarith
        have h13 : x = 1 ∨ x = -1 := by
          rw [sq_eq_one_iff] at h12
          tauto
        cases h13 with
        | inl h14 =>
          right
          right
          linarith
        | inr h14 =>
          left
          linarith
      · -- 2 * x^2 + 3 = 0
        nlinarith [sq_nonneg x]
  · -- Backward implication: if x ∈ {-1, 0, 1}, then the equation holds
    rintro (h | h | h)
    · -- x = -1
      rw [h]
      norm_num
    · -- x = 0
      rw [h]
      norm_num
    · -- x = 1
      rw [h]
      norm_num