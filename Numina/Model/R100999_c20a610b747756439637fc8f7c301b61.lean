import Mathlib

theorem algebra_314075 (a b c : ℝ)
    (h₀ : a^2 - b * c - 6 * a + 3 = 0) (h₁ : b^2 + c^2 + b * c - 2 * a - 1 = 0) :
    (10 - 2 * √19) / 3 ≤ a ∧ a ≤ (10 + 2 * √19) / 3 := by

  have h2 : b * c = a^2 - 6 * a + 3 := by
    nlinarith

  have h3 : 3 * (b * c) ≤ 2 * a + 1 := by
    nlinarith [sq_nonneg (b - c)]

  rw [h2] at h3

  have h4 : 3 * a^2 - 20 * a + 8 ≤ 0 := by
    nlinarith

  constructor
  · -- Prove (10 - 2 * √19) / 3 ≤ a
    nlinarith [Real.sqrt_nonneg 19, Real.sq_sqrt (show (19 : ℝ) ≥ 0 by norm_num)]

  · -- Prove a ≤ (10 + 2 * √19) / 3
    nlinarith [Real.sqrt_nonneg 19, Real.sq_sqrt (show (19 : ℝ) ≥ 0 by norm_num)]