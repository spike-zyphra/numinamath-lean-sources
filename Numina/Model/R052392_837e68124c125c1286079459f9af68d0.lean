import Mathlib

theorem inequalities_47785 (a A b B : ℝ) (h₀ : 0 < a) (h₁ : 0 < b)
    (h₂ : |A - 3 * a| ≤ 1 - a) (h₃ : |B - 3 * b| ≤ 1 - b) :
    |(A * B) / 3 - 3 * a * b| - 3 * a * b ≤ 1 - a * b := by 
  cases' abs_cases (A * B / 3 - 3 * a * b) with h h <;> 
    nlinarith [abs_le.mp h₂, abs_le.mp h₃, mul_pos h₀ h₁, 
      sq_nonneg (A - 3 * a), sq_nonneg (B - 3 * b), 
      sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1)]