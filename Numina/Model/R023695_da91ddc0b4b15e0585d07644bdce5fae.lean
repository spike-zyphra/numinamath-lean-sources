import Mathlib

theorem algebra_163081 (a b c : ℝ) (h₀ : a^2 + 2 * b^2 - 2 * b * c = 16) (h₁ : 2 * a * b - c^2 = 16) :
    (a = 4 ∧ b = 4 ∧ c = 4) ∨ (a = -4 ∧ b = -4 ∧ c = -4) := by
  have h2 : (a - b) ^ 2 + (b - c) ^ 2 = 0 := by
    nlinarith
  have h3 : a - b = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c)]
  have h4 : b - c = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c)]
  have h5 : a = b := by linarith
  have h6 : b = c := by linarith
  have h7 : a ^ 2 = 16 := by
    have eq1 : b = a := by linarith
    have eq2 : c = a := by linarith
    rw [show b = a by linarith] at h₁
    rw [show c = a by linarith] at h₁
    nlinarith
  have h8 : a = 4 ∨ a = -4 := by
    have h9 : a ^ 2 - 16 = 0 := by linarith
    have h10 : (a - 4) * (a + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h10) with h11 h12
    · -- Case a - 4 = 0
      left
      linarith
    · -- Case a + 4 = 0
      right
      linarith
  cases h8 with
  | inl ha4 =>
    have hb4 : b = 4 := by linarith [h5, ha4]
    have hc4 : c = 4 := by linarith [h6, hb4]
    left
    constructor
    · exact ha4
    constructor
    · exact hb4
    · exact hc4
  | inr ha4 =>
    have hb4 : b = -4 := by linarith [h5, ha4]
    have hc4 : c = -4 := by linarith [h6, hb4]
    right
    constructor
    · exact ha4
    constructor
    · exact hb4
    · exact hc4