import Mathlib

theorem algebra_251477 (x : ℝ) (hx : x^2 > 0) : Real.logb 2 (x^2) = 2 ↔ x = 2 ∨ x = -2 := by
  constructor
  · -- Assume Real.logb 2 (x^2) = 2, prove x = 2 ∨ x = -2
    intro h_eq
    have h1 : x^2 = (2 : ℝ) ^ 2 := by
      have h2 : Real.logb 2 (x^2) = 2 := h_eq
      have h3 : x^2 = (2 : ℝ) ^ (Real.logb 2 (x^2)) := by
        rw [Real.rpow_logb]
        all_goals
          nlinarith
      rw [h2] at h3
      norm_num at h3 ⊢
      linarith
    have h2 : x^2 = (4 : ℝ) := by
      nlinarith
    have h3 : x = 2 ∨ x = -2 := by
      have h4 : x^2 - (4 : ℝ) = 0 := by linarith
      have h5 : (x - 2) * (x + 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.1 h5) with
      | inl h6 =>
        left
        linarith
      | inr h7 =>
        right
        linarith
    exact h3
  · -- Assume x = 2 ∨ x = -2, prove Real.logb 2 (x^2) = 2
    rintro (h | h)
    · -- x = 2
      rw [h]
      have h1 : (2 : ℝ) ^2 = (4 : ℝ) := by
        norm_num
      rw [h1]
      have h2 : Real.logb 2 (4) = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith
    · -- x = -2
      rw [h]
      have h2 : (-2 : ℝ) ^ 2 = (4 : ℝ) := by
        norm_num
      rw [h2]
      have h2 : Real.logb 2 (4) = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith