import Mathlib

theorem algebra_200657 (a b : ℝ) :
    32 * a^2 * b^2 * (a^2 + b^2)^2 + (a^2 - b^2)^4 +
    8 * a * b * (a^2 + b^2) *
    Real.sqrt (16 * a^2 * b^2 * (a^2 + b^2)^2 + (a^2 - b^2)^4) =
    (a + b)^8 := by
  have h1 : Real.sqrt (16 * a^2 * b^2 * (a^2 + b^2)^2 + (a^2 - b^2)^4) =
      a^4 + 6 * a^2 * b^2 + b^4 := by
    have h2 : (16 * a^2 * b^2 * (a^2 + b^2)^2 + (a^2 - b^2)^4 : ℝ) =
        (a^4 + 6 * a^2 * b^2 + b^4) ^ 2 := by
      ring_nf
    rw [h2]
    have h_nonneg : 0 ≤ (a^4 + 6 * a^2 * b^2 + b^4 : ℝ) := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 + b^2), sq_nonneg (a * b)]
    rw [Real.sqrt_sq (by linarith)]
  rw [h1]
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b), sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a^3 - b^3), sq_nonneg (a^3 + b^3)]