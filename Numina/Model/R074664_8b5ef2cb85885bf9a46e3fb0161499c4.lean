import Mathlib

theorem algebra_327961 {a b : ℝ} (h : (1 / 2) * a - a * b + b ^ 2 + 2 = 0) :
    a ≤ -2 ∨ a ≥ 4 := by
  have h1 : (b - a / 2) ^ 2 ≥ 0 := by 
    apply sq_nonneg 
  have h2 : (a ^ 2) / 4 - (1 / 2) * a - 2 ≥ 0 := by
    nlinarith [h, h1]
  have h3 : a^2 - 2 * a - 8 ≥ 0 := by
    nlinarith [h2]
  have h4 : (a - 4) * (a + 2) ≥ 0 := by 
    nlinarith [h3]
  by_cases h5 : a ≤ -2 
  · left 
    exact h5
  · -- Since a > -2 and we have (a - 4) * (a + 2) ≥ 0, must have a ≥ 4
    have h6 : a > -2 := by linarith
    have h7 : a ≥ 4 := by 
      nlinarith [h4, h6]
    right 
    linarith [h7]