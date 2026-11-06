import Mathlib

theorem algebra_297260 (a b c : ℝ)
    (h₁ : a^2 - b * c - 6 * a + 1 = 0)
    (h₂ : b^2 + c^2 + b * c - 2 * a - 1 = 0) :
    (10 - Real.sqrt 94) / 3 ≤ a ∧ a ≤ (10 + Real.sqrt 94) / 3 := by
  have hbc : b * c = a^2 - 6 * a + 1 := by linarith
  have heq : b ^ 2 + c ^ 2 = 8 * a - a ^ 2 := by
    have h₂' : b ^ 2 + c ^ 2 + (b * c) - 2 * a - 1 = 0 := by linarith [h₂, hbc]
    nlinarith
  have h3 : b ^ 2 + c ^ 2 ≥ 2 * (b * c) := by
    linarith [sq_nonneg (b - c)]
  rw [heq, hbc] at h3
  have h4 : 20 * a - 3 * a^2 - 2 ≥ 0 := by
    nlinarith
  have h5 : 3 * a^2 - 20 * a + 2 ≤ 0 := by
    nlinarith
  constructor
  · -- To prove (10 - Real.sqrt 94) / 3 ≤ a
    have h6 : (10 - Real.sqrt 94) / 3 ≤ a := by
      nlinarith [Real.sqrt_pos.mpr (show (94: ℝ) > 0 by norm_num),
        Real.sq_sqrt (show (0: ℝ) ≤ (94: ℝ) by norm_num),
        h5]
    exact h6
  · -- To prove a ≤ (10 + Real.sqrt 94) / 3
    have h7 : a ≤ (10 + Real.sqrt 94) / 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (94: ℝ) > 0 by norm_num),
        Real.sq_sqrt (show (0: ℝ) ≤ (94: ℝ) by norm_num),
        h5]
    exact h7