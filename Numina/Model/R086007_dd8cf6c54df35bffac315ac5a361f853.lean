import Mathlib

theorem inequalities_83992 (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    Real.sqrt (a ^ 3 * b ^ 3) + Real.sqrt ((1 - a ^ 2) * (1 - a * b) * (1 - b ^ 2)) ≤ 1 := by
  have h1 : 0 ≤ a := ha.1
  have h2 : a ≤ 1 := ha.2
  have h3 : 0 ≤ b := hb.1
  have h4 : b ≤ 1 := hb.2
  have h5 : 0 ≤ a * b := mul_nonneg h1 h3
  have h6 : a * b ≤ 1 := by nlinarith [h1, h2, h3, h4]
  have h7 : Real.sqrt (a ^ 3 * b ^ 3) ≤ a * b := by
    have h8 : a ^ 3 * b ^ 3 ≤ (a * b) ^ 2 := by nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1)]
    have h9 : Real.sqrt (a ^ 3 * b ^ 3) ≤ Real.sqrt ((a * b) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h10 : Real.sqrt ((a * b) ^ 2) = a * b := by
      rw [Real.sqrt_sq (by nlinarith)]
    linarith
  have h11 : Real.sqrt ((1 - a ^ 2) * (1 - a * b) * (1 - b ^ 2)) ≤ 1 - a * b := by
    have h12 : (1 - a ^ 2) * (1 - a * b) * (1 - b ^ 2) ≤ (1 - a * b) ^ 2 := by
      nlinarith [sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1)]
    have h13 : Real.sqrt ((1 - a ^ 2) * (1 - a * b) * (1 - b ^ 2)) ≤ Real.sqrt ((1 - a * b) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h14 : Real.sqrt ((1 - a * b) ^ 2) = 1 - a * b := by
      rw [Real.sqrt_sq (by nlinarith)]
    linarith
  linarith