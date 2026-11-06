import Mathlib

theorem inequalities_85174 (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1) :
    a^2 + b^2 - c^2 - d^2 ≤ Real.sqrt (2 + 4 * (a * c + b * d)) := by
  have h1 : 0 ≤ 2 + 4 * (a * c + b * d) := by
    nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (a * c + b * d + 1 / 2), sq_nonneg (a * c - b * d), sq_nonneg (a * b - c * d), h, sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2)]
  have h2 : a^2 + b^2 - c^2 - d^2 ≤ Real.sqrt (2 + 4 * (a * c + b * d)) := by
    have h3 : (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) ^ 2 ≤ 2 + 4 * (a * c + b * d) := by
      nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (a * c + b * d - (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) / 2), sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a + c), sq_nonneg (b + d), sq_nonneg (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2), sq_nonneg (a * d - b * c), sq_nonneg (a * c + b * d), h]
    have h4 : Real.sqrt ((a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) ^ 2) ≤ Real.sqrt (2 + 4 * (a * c + b * d)) := by
      apply Real.sqrt_le_sqrt (show (a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) ^ 2 ≤ 2 + 4 * (a * c + b * d) by nlinarith)
    have h5 : Real.sqrt ((a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2) ^ 2) = |a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h5] at h4
    cases' abs_le.mp (show |a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2| ≤ Real.sqrt (2 + 4 * (a * c + b * d)) by linarith) with h6 h7
    all_goals nlinarith
  linarith