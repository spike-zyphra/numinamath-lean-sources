import Mathlib

theorem algebra_166265 (x y : ℝ) (h₀ : x^4 + y^4 = 17) (h₁ : x^2 + y^2 = 5) :
    (x, y) = (2, 1) ∨ (x, y) = (1, 2) ∨ (x, y) = (-2, 1) ∨ (x, y) = (1, -2) ∨
    (x, y) = (2, -1) ∨ (x, y) = (-1, 2) ∨ (x, y) = (-2, -1) ∨ (x, y) = (-1, -2) := by

  have h2 : (x^2) * (y^2) = 4 := by
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x * y)]

  have h3 : x * y = 2 ∨ x * y = -2 := by
    have h4 : (x * y) ^ 2 = 4 := by
      nlinarith
    have h5 : x * y = 2 ∨ x * y = -2 := by
      have h6 : (x * y) ^ 2 - 4 = 0 := by linarith
      have h7 : (x * y - 2) * (x * y + 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h7) with
      | inl h8 =>
        left
        linarith
      | inr h9 =>
        right
        linarith
    exact h5

  cases h3 with
  | inl h4 =>
    have h5 : (x + y) ^ 2 = 9 := by
      nlinarith [sq_nonneg (x - y)]
    have h6 : x + y = 3 ∨ x + y = -3 := by
      have h7 : (x + y) ^ 2 - 9 = 0 := by linarith
      have h8 : (x + y - 3) * (x + y + 3) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h8) with
      | inl h9 =>
        left
        linarith
      | inr h10 =>
        right
        linarith

    cases h6 with
    | inl h7 =>
      have h8 : y = 3 - x := by linarith
      rw [show y = 3 - x by linarith] at h₁ h4
      have h9 : (x - 1) * (x - 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h9) with
      | inl h10 =>
        have h11 : x = 1 := by linarith
        have h12 : y = 2 := by linarith
        simp [h11, h12]
      | inr h11 =>
        have h12 : x = 2 := by linarith
        have h13 : y = 1 := by linarith
        simp [h12, h13]
    | inr h7 =>
      have h8 : y = -3 - x := by linarith
      rw [show y = -3 - x by linarith] at h₁ h4
      have h9 : (x + 1) * (x + 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h9) with
      | inl h10 =>
        have h11 : x = -1 := by linarith
        have h12 : y = -2 := by linarith
        simp [h11, h12]
      | inr h11 =>
        have h12 : x = -2 := by linarith
        have h13 : y = -1 := by linarith
        simp [h12, h13]
  | inr h4 =>
    have h5 : (x + y) ^ 2 = 1 := by
      nlinarith [sq_nonneg (x - y)]
    have h6 : x + y = 1 ∨ x + y = -1 := by 
      have h7 : (x + y) ^ 2 - 1 = 0 := by linarith
      have h8 : (x + y - 1) * (x + y + 1) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h8) with
      | inl h9 =>
        left
        linarith
      | inr h10 =>
        right
        linarith

    cases h6 with
    | inl h7 =>
      have h8 : y = 1 - x := by linarith
      rw [show y = 1 - x by linarith] at h₁ h4
      have h9 : (x - 2) * (x + 1) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h9) with
      | inl h10 =>
        have h11 : x = 2 := by linarith
        have h12 : y = -1 := by linarith
        simp [h11, h12]
      | inr h11 =>
        have h12 : x = -1 := by linarith
        have h13 : y = 2 := by linarith
        simp [h12, h13]
    | inr h7 =>
      have h8 : y = -1 - x := by linarith
      rw [show y = -1 - x by linarith] at h₁ h4
      have h9 : (x + 2) * (x - 1) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h9) with
      | inl h10 =>
        have h11 : x = -2 := by linarith
        have h12 : y = 1 := by linarith
        simp [h11, h12]
      | inr h11 =>
        have h12 : x = 1 := by linarith
        have h13 : y = -2 := by linarith
        simp [h12, h13]