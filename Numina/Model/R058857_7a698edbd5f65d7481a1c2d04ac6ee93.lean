import Mathlib

theorem algebra_13266 {a b c : ℝ} (h₀ : a + b + c = 2) (h₁ : a^2 + b^2 + c^2 = 14) (h₂ : a^3 + b^3 + c^3 = 29) :
    a^4 + b^4 + c^4 = 122 := by
  have h₃ : a * b + b * c + c * a = -5 := by
    have h₄ : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + b * c + c * a) := by
      ring
    rw [h₀] at h₄
    linarith

  -- Derive the value of a*b*c from the identity for sum of cubes
  have h₄' : a^3 + b^3 + c^3 = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) + 3 * (a * b * c) := by
    ring
  rw [h₀, h₃] at h₄'
  have h₅ : 29 = 38 + 3 * (a * b * c) := by
    linarith [h₂, h₄']

  -- Rearranging to find a*b*c = -3
  have h6 : 3 * (a * b * c) = -9 := by
    linarith
  have h₇ : a * b * c = -3 := by
    linarith

  -- Now compute a^4 + b^4 + c^4 using the square of the sum of squares
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a + b + c - 2), sq_nonneg (a * b + b * c + c * a + 5),
            sq_nonneg (a * b * c + 3)]

  <;> nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a + b + c - 2), sq_nonneg (a * b + b * c + c * a + 5),
            sq_nonneg (a * b * c + 3)]
  <;> nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a + b + c - 2), sq_nonneg (a * b + b * c + c * a + 5),
            sq_nonneg (a * b * c + 3)]
  all_goals
    nlinarith
  all_goals
    omega
  <;> nlinarith
  <;> ring_nf
  <;> nlinarith
  <;> nlinarith [sq_nonneg (a + b + c - 2), sq_nonneg (a * b + b * c + c * a + 5), sq_nonneg (a * b * c + 3)]
  <;> nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  <;> nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals
    nlinarith