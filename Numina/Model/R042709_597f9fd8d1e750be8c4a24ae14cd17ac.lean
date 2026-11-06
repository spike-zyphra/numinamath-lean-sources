import Mathlib

theorem algebra_272357 {x y z : ℝ} (h₀ : x + y + z = 3) (h₁ : x^3 + y^3 + z^3 = 15)
    (h₂ : x^4 + y^4 + z^4 = 35) (h₃ : x^2 + y^2 + z^2 < 10) :
    x^5 + y^5 + z^5 = 83 := by
  have h41 : x^2 + y^2 + z^2 = (x + y + z) ^ 2 - 2 * (x * y + y * z + z * x) := by
    ring
  rw [h₀] at h41
  have eq1 : 3 * (x * y + y * z + z * x) - (x * y * z) = 4 := by
    have h5 : x^3 + y^3 + z^3 = (x + y + z) ^ 3 - 3 * (x + y + z) * (x * y + y * z + z * x) + 3 * (x * y * z) := by
      ring
    rw [h₀] at h5
    linarith
  have eq2 : x^4 + y^4 + z^4 = (x^2 + y^2 + z^2) ^ 2 - 2 * ((x * y + y * z + z * x) ^ 2 - 2 * (x * y * z) * (x + y + z)) := by
    ring
  rw [h₂] at eq2
  rw [h41] at eq2
  rw [h₀] at eq2
  have h5 : (x * y + y * z + z * x) ^ 2 = 1 := by
    nlinarith [sq_nonneg (x * y + y * z + z * x), sq_nonneg (x * y * z - -1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have h6 : x * y + y * z + z * x = 1 ∨ x * y + y * z + z * x = -1 := by
    have h7 : (x * y + y * z + z * x) ^ 2 - 1 = 0 := by linarith
    have h8 : (x * y + y * z + z * x - 1) * (x * y + y * z + z * x + 1) = 0 := by
      linarith
    cases (mul_eq_zero.1 h8) with
    | inl h9 =>
      left
      linarith
    | inr h10 =>
      right
      linarith
  cases h6 with
  | inl h7 =>
    have h8 : x * y * z = -1 := by
      nlinarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  | inr h7 =>
    have h9 : x * y + y * z + z * x = -1 := by
      linarith
    have h10 : x^2 + y^2 + z^2 = 11 := by
      nlinarith
    nlinarith