import Mathlib

theorem algebra_212625 (x : ℝ) : Real.sqrt (x^2 - 4 * x + 13) + 1 = 2 * x ↔ x = 2 := by
  constructor
  · -- Assume $\sqrt{x^2 - 4x + 13} + 1 = 2x$ prove $x = 2$
    intro h
    have h1 : Real.sqrt (x^2 - 4 * x + 13) = 2 * x - 1 := by linarith
    have h2 : Real.sqrt (x^2 - 4 * x + 13) ≥ 0 := by
      positivity
    have h3 : (2 * x - 1) ≥ 0 := by linarith [h1, h2]
    have h4 : (Real.sqrt (x^2 - 4 * x + 13))^2 = (2 * x - 1)^2 := by
      rw [h1]
    have h5 : (Real.sqrt (x^2 - 4 * x + 13))^2 = x^2 - 4 * x + 13 := Real.sq_sqrt (by
      nlinarith [sq_nonneg (x - 2)]
    )
    rw [h5] at h4
    have h6 : (2 * x - 1)^2 = 4 * x^2 - 4 * x + 1 := by ring
    rw [h6] at h4
    have h7 : 3 * x^2 = 12 := by linarith
    have h8 : x^2 = 4 := by linarith
    have h9 : x = 2 ∨ x = -2 := by
      have h10 : (x - 2) * (x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- x - 2 = 0 → x = 2
        left
        linarith
      · -- x + 2 = 0 → x = -2
        right
        linarith
    cases' h9 with h10 h11
    · -- x = 2
      exact h10
    · -- x = -2, which should be invalid
      have h12 : x = -2 := h11
      rw [h12] at h3
      nlinarith
  · -- Assume x = 2, prove √(x^2 - 4 * x + 13) + 1 = 2 * x
    intro h
    rw [h]
    have h1 : Real.sqrt ((2 : ℝ) ^ 2 - 4 * (2 : ℝ) + 13) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    all_goals norm_num