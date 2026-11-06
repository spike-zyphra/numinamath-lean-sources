import Mathlib

open Real

theorem inequalities_597707 (a b c : ℝ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c)
    (h₃ : a ≤ b) (h₄ : b < c) (h₅ : a^2 + b^2 = c^2) :
    1 / a + 1 / b + 1 / c ≥ (5 + 3 * √2) / (a + b + c) := by
  have h6 : 0 < a * b * c := by
    positivity
  have h7 : 0 < a + b + c := by
    linarith
  have h8 : 1 / a + 1 / b + 1 / c - (5 + 3 * Real.sqrt 2) / (a + b + c) ≥ 0 := by
    have h9 : 0 < a * b * c * (a + b + c) := by
      positivity
    have h10 : (1 / a + 1 / b + 1 / c - (5 + 3 * Real.sqrt 2) / (a + b + c)) =
        ( (b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) ) - (5 + 3 * Real.sqrt 2) * (a * b * c) ) / ( (a * b * c) * (a + b + c) ) := by
      field_simp
      <;> ring
      <;> field_simp
      <;> ring
    rw [h10]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a * (Real.sqrt 2 - 1) + b * (Real.sqrt 2 - 1) - c), sq_nonneg (a * (Real.sqrt 2 - 1) - b), sq_nonneg (a - b), sq_nonneg (a + b - c), sq_nonneg (a * Real.sqrt 2 - b), sq_nonneg (a * Real.sqrt 2 - c), sq_nonneg (b - c / Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (c - a * Real.sqrt 2), sq_nonneg (a - b), mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₀ h₂, Real.sqrt_nonneg 2, sq_nonneg (a * (Real.sqrt 2 - 1)), sq_nonneg (b - a * (Real.sqrt 2 - 1)), sq_nonneg (c - a * Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), mul_pos h₀ (show 0 < a * b by nlinarith)]
    all_goals
      positivity
  linarith [h8]