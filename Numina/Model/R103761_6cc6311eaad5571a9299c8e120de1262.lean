import Mathlib

theorem inequalities_601313 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 4 + b ^ 4 = 1) :
    (a ^ ((1 : ℝ) / 3) + b ≥ Real.sqrt (a ^ 2) + b ^ 2) := by
  have h1 : Real.sqrt (a ^ 2) = a := by
    rw [Real.sqrt_sq]
    linarith
  have h2 : a ≤ 1 := by nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), h, mul_pos ha hb]
  have h3 : b ≤ 1 := by nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), h, mul_pos ha hb]
  have h4 : a ^ ((1 : ℝ) / 3) ≥ a := by
    have h9 : 0 < a := ha
    have h10 : a ≤ 1 := h2
    have h11 : a ^ ((1 : ℝ) / 3) ≥ a := by
      have h12 : a ^ (1 / 3 : ℝ) ≥ a ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_ge
        all_goals nlinarith
      have h13 : a ^ (1 : ℝ) = a := by
        simp
      rw [h13] at h12
      linarith
    linarith
  have h5 : b ≥ b ^ 2 := by nlinarith [sq_nonneg (b - 1), h3, mul_pos ha hb]
  have h6 : Real.sqrt (a ^ 2) = a := h1
  linarith [h4, h5, h6]