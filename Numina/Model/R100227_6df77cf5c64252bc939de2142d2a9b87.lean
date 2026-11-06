import Mathlib

theorem algebra_140472 (x y : ℝ) (h₁ : |x + y| = 3) (h₂ : x * y = -10) :
    (x = 5 ∧ y = -2) ∨ (x = -2 ∧ y = 5) ∨ (x = 2 ∧ y = -5) ∨ (x = -5 ∧ y = 2) := by
  cases eq_or_eq_neg_of_abs_eq h₁ with
  | inl h3 =>
    -- Case where x + y = 3
    have h4 : y = 3 - x := by linarith
    rw [h4] at h₂
    -- Substituting y = 3 - x into x * y = -10
    -- We get x * (3 - x) = -10
    -- Expanding: 3x - x^2 = -10
    -- Rearranging: x^2 - 3x - 10 = 0
    have h5 : x ^ 2 - 3 * x - 10 = 0 := by
      linarith
    -- Solving quadratic equation: (x - 5) * (x + 2) = 0
    have h6 : (x - 5) * (x + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case x = 5
      left
      constructor
      · -- Show x = 5
        linarith
      · -- Show y = -2
        linarith [h4, h7]
    · -- Case x = -2
      right
      left
      constructor
      · -- Show x = -2
        linarith
      · -- Show y = 5
        linarith [h4, h8]
  | inr h3 =>
    -- Case where x + y = -3
    have h4 : y = -3 - x := by linarith
    rw [h4] at h₂
    -- Substituting y = -3 - x into x * y = -10
    -- We get x * (-3 - x) = -10
    -- Expanding: -3x - x^2 = -10
    -- Rearranging: x^2 + 3x - 10 = 0
    have h5 : x ^ 2 + 3 * x - 10 = 0 := by
      linarith
    -- Solving quadratic equation: (x - 2) * (x + 5) = 0
    have h6 : (x - 2) * (x + 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case x = 2
      right
      right
      left
      constructor
      · -- Show x = 2
        linarith
      · -- Show y = -5
        linarith [h4, h7]
    · -- Case x = -5
      right
      right
      right
      constructor
      · -- Show x = -5
        linarith
      · -- Show y = 2
        linarith [h4, h8]