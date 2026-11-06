import Mathlib

theorem algebra_245662 {p q : ℝ} (x : ℝ) (hx : x^2 + p * x + q = 0) (lambda : ℝ)
    (hl : lambda > 0) :
    x ≥ (4 * q - (p + lambda)^2) / (4 * lambda) := by
  have h1 : q = -x^2 - p * x := by linarith
  have h4 : (4 * lambda) * x ≥ 4 * q - (p + lambda)^2 := by
    have h5 : -4 * x^2 - 4 * p * x - (p + lambda)^2 ≤ (4 * lambda) * x := by
      nlinarith [sq_nonneg (2 * x + (p + lambda)), sq_nonneg (x + (p + lambda) / 2), sq_nonneg (x + (p + lambda) / 2 - lambda), sq_nonneg (x - (- (p + lambda) / 2)), mul_pos (show (0 : ℝ) < 4 by norm_num) (show 0 < lambda by linarith)]
    have h3 : 4 * q = -4 * x^2 - 4 * p * x := by
      have hq1 : q = -x^2 - p * x := by linarith
      linarith [hq1]
    nlinarith [h5, h3]
  have h5 : (4 * q - (p + lambda)^2) / (4 * lambda) ≤ x := by
    have h6 : 4 * lambda > 0 := by nlinarith
    have h7 : (4 * q - (p + lambda)^2) / (4 * lambda) ≤ x := by
      apply (div_le_iff₀ h6).mpr
      nlinarith [h4]
    linarith
  linarith [h5]