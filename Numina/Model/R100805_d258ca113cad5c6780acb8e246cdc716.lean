import Mathlib

open Real

theorem inequalities_603475 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    sqrt (2 * a^2 + 5 * a * b + 2 * b^2) +
    sqrt (2 * a^2 + 5 * a * c + 2 * c^2) +
    sqrt (2 * b^2 + 5 * b * c + 2 * c^2) ≤
    3 * (a + b + c) := by

  have h1 : sqrt (2 * a^2 + 5 * a * b + 2 * b^2) ≤ (3 / 2) * (a + b) := by
    have h1 : 2 * a^2 + 5 * a * b + 2 * b^2 ≤ (9 / 4) * (a + b) ^ 2 := by
      nlinarith [sq_nonneg (a - b)]
    have h2 : sqrt (2 * a^2 + 5 * a * b + 2 * b^2) ≤ sqrt ((9 / 4) * (a + b) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h3 : sqrt ((9 / 4) * (a + b) ^ 2) = (3 / 2) * (a + b) := by
      have h4 : (9 / 4 : ℝ) * (a + b) ^ 2 = ((3 / 2) * (a + b)) ^ 2 := by
        ring
      rw [h4]
      rw [Real.sqrt_sq (by positivity)]
    linarith

  have h2 : sqrt (2 * a^2 + 5 * a * c + 2 * c^2) ≤ (3 / 2) * (a + c) := by
    have h1 : 2 * a^2 + 5 * a * c + 2 * c^2 ≤ (9 / 4) * (a + c) ^ 2 := by
      nlinarith [sq_nonneg (a - c)]
    have h2 : sqrt (2 * a^2 + 5 * a * c + 2 * c^2) ≤ sqrt ((9 / 4) * (a + c) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h3 : sqrt ((9 / 4) * (a + c) ^ 2) = (3 / 2) * (a + c) := by
      have h4 : (9 / 4 : ℝ) * (a + c) ^ 2 = ((3 / 2) * (a + c)) ^ 2 := by
        ring
      rw [h4]
      rw [Real.sqrt_sq (by positivity)]
    linarith

  have h3 : sqrt (2 * b^2 + 5 * b * c + 2 * c^2) ≤ (3 / 2) * (b + c) := by
    have h1 : 2 * b^2 + 5 * b * c + 2 * c^2 ≤ (9 / 4) * (b + c) ^ 2 := by
      nlinarith [sq_nonneg (b - c)]
    have h2 : sqrt (2 * b^2 + 5 * b * c + 2 * c^2) ≤ sqrt ((9 / 4) * (b + c) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h3 : sqrt ((9 / 4) * (b + c) ^ 2) = (3 / 2) * (b + c) := by
      have h4 : (9 / 4 : ℝ) * (b + c) ^ 2 = ((3 / 2) * (b + c)) ^ 2 := by
        ring
      rw [h4]
      rw [Real.sqrt_sq (by positivity)]
    linarith

  linarith [h1, h2, h3]