import Mathlib

theorem algebra_322835 (a b c : ℝ)
    (h₀ : a^2 - b * c - 8 * a + 7 = 0) (h₁ : b^2 + c^2 + b * c - 6 * a + 6 = 0) :
    1 ≤ a ∧ a ≤ 9 := by

  have h2 : b^2 + c^2 ≥ 2 * (b * c) := by 
    linarith [sq_nonneg (b - c)]

  have h3 : b^2 + c^2 + b * c = 6 * a - 6 := by
    linarith

  have h4 : 6 * a - 6 ≥ 3 * (b * c) := by 
    nlinarith [h2, h3]

  have h5 : b * c = a^2 - 8 * a + 7 := by 
    linarith

  have h6 : 2 * a - 2 ≥ a^2 - 8 * a + 7 := by 
    nlinarith [h4, h5]

  have h7 : a^2 - 10 * a + 9 ≤ 0 := by 
    nlinarith

  constructor
  · -- Prove 1 ≤ a
    nlinarith 
  · -- Prove a ≤ 9
    nlinarith