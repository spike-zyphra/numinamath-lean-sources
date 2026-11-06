import Mathlib

theorem algebra_148010 (a b c : ℝ)
    (h₀ : a^2 - b * c - 8 * a + 7 = 0)
    (h₁ : b^2 + c^2 + b * c - 6 * a + 6 = 0) :
    1 ≤ a ∧ a ≤ 9 := by

  have h2 : (b + c - (a - 1)) * (b + c + (a - 1)) = 0 := by
    nlinarith [sq_nonneg (b - c)]

  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Assume b + c = a - 1
    have hab : b + c = a - 1 := by linarith
    have h3' : (a - 1) ^ 2 - 4 * (a^2 - 8 * a + 7) ≥ 0 := by
      nlinarith [sq_nonneg (b - c)]

    have h5'' : a^2 - 10 * a + 9 ≤ 0 := by
      nlinarith

    have h4 : 1 ≤ a := by
      nlinarith

    have h5 : a ≤ 9 := by
      nlinarith

    exact ⟨h4, h5⟩
  · -- Assume b + c = 1 - a
    have hab : b + c = 1 - a := by linarith
    have h4' : (1 - a) ^ 2 - 4 * (a^2 - 8 * a + 7) ≥ 0 := by
      nlinarith [sq_nonneg (b - c)]

    have h5'' : a^2 - 10 * a + 9 ≤ 0 := by
      nlinarith

    have h4 : 1 ≤ a := by
      nlinarith

    have h5 : a ≤ 9 := by
      nlinarith

    exact ⟨h4, h5⟩