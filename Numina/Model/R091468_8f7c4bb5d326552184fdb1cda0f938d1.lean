import Mathlib

theorem algebra_143458 (a b c : ℝ)
    (h₀ : a^2 - b * c - 8 * a + 7 = 0) (h₁ : b^2 + c^2 + b * c - 6 * a + 6 = 0) :
    1 ≤ a ∧ a ≤ 9 := by
  have h2 : b^2 + c^2 ≥ 2 * (b * c) := by
    linarith [sq_nonneg (b - c)]
  
  have h3 : b^2 + c^2 + b * c ≥ 3 * (b * c) := by
    linarith [h2]
  
  have h4 : 3 * (b * c) ≤ 6 * a - 6 := by
    nlinarith [h₁, h3]

  have h5 : b * c = a^2 - 8 * a + 7 := by
    linarith [h₀]

  rw [h5] at h4

  have h6 : a^2 - 10 * a + 9 ≤ 0 := by 
    nlinarith
  
  have h7 : (a - 1) * (a - 9) ≤ 0 := by 
    nlinarith [h6]

  constructor
  · -- Prove 1 ≤ a
    nlinarith
  · -- Prove a ≤ 9
    nlinarith