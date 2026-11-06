import Mathlib

theorem number_theory_13406 (k : ℝ) (hk : k^7 = 893871739) : k = 19 := by
  have h8 : k^7 - 893871739 = 0 := by linarith [hk]

  have h9 : k^7 - 893871739 = (k - 19) * (k^6 + 19*k^5 + 361*k^4 + 6859*k^3 + 130321*k^2 + 2476099*k + 47045881) := by
    ring

  rw [h9] at h8

  cases' (mul_eq_zero.1 h8) with h10 h11

  · -- The factor k - 19 is zero, so k = 19
    linarith

  · -- Show that the polynomial is not zero
    nlinarith [sq_nonneg (k^3), sq_nonneg (k^2 - 19^2 * k), sq_nonneg (k^2 - 19^2), sq_nonneg (k * 19^2), sq_nonneg (k^3 - 19^3), sq_nonneg (k^3 + 19^3), sq_nonneg (k - 19), sq_nonneg (k + 19), sq_nonneg (k^2 - 19*k), sq_nonneg (k^2 + 19*k), sq_nonneg (k^3 - 19^3), sq_nonneg (k^3 + 19^3), sq_nonneg (k^3 - k * 19^2), sq_nonneg (k^3 + k * 19^2), sq_nonneg (k^2 - 19*k), sq_nonneg (k^2 + 19*k), sq_nonneg (k^3), sq_nonneg (k^2 - 19^2 * k), sq_nonneg (k^2 - 19^2), sq_nonneg (k * 19^2)]