import Mathlib

theorem algebra_305564 (x : ℝ) : (1 + x ^ 2) ^ 2 = 4 * x * (1 - x ^ 2) ↔ x = -1 + Real.sqrt 2 ∨ x = -1 - Real.sqrt 2 := by
  constructor
  · -- Assume $(1 + x^2)^2 = 4x(1 - x^2)$, prove $x = -1 + \sqrt{2}$ or $x = -1 - \sqrt{2}$.
    intro h
    have h1 : (1 + x ^ 2) ^ 2 - 4 * x * (1 - x ^ 2) = 0 := by linarith
    have h2 : (x ^ 2 + 2 * x - 1) ^ 2 = 0 := by
      nlinarith [h1]
    have h3 : x ^ 2 + 2 * x - 1 = 0 := by
      rw [sq_eq_zero_iff] at h2
      linarith
    have h4 : (x - (-1 + Real.sqrt 2)) * (x - (-1 - Real.sqrt 2)) = 0 := by
      have hquad : x ^ 2 + 2 * x - 1 = (x - (-1 + Real.sqrt 2)) * (x - (-1 - Real.sqrt 2)) := by
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        linarith
      rw [hquad] at h3
      linarith
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- First factor is zero: x - (-1 + sqrt 2) = 0
      left
      linarith
    · -- Second factor is zero: x - (-1 - sqrt 2) = 0
      right
      linarith
  · -- Assume x = -1 + sqrt 2 or x = -1 - sqrt 2, prove (1 + x^2)^2 = 4 * x * (1 - x^2)
    rintro (h | h)
    · -- Case x = -1 + sqrt 2
      rw [h]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    · -- Case x = -1 - sqrt 2
      rw [h]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]