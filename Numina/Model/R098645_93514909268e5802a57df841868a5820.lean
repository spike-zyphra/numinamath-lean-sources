import Mathlib

theorem algebra_152278 (x : ℝ) (hx : x^2 - abs x - 1 = 0) :
    x = (-(1 : ℝ) + Real.sqrt 5) / 2 ∨ x = (-1 - Real.sqrt 5) / 2 ∨
    x = (1 + Real.sqrt 5) / 2 ∨ x = (1 - Real.sqrt 5) / 2 := by

  by_cases h : x ≥ 0
  · -- In this case, |x| = x
    rw [abs_of_nonneg h] at hx
    have h1 : x^2 - x - 1 = 0 := by linarith

    have h2 : x^2 - x - 1 = (x - (1 + Real.sqrt 5) / 2) * (x - (1 - Real.sqrt 5) / 2) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

    rw [h2] at h1
    cases' (mul_eq_zero.mp h1) with h3 h4
    · -- Case where x = (1 + sqrt 5)/2
      have hx_eq : x = (1 + Real.sqrt 5) / 2 := by linarith
      simp [hx_eq]
      <;> linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

    · -- Case where x = (1 - sqrt 5)/2 (which is negative)
      have h5 : x = (1 - Real.sqrt 5) / 2 := by linarith
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

  · -- Case 2: x < 0
    rw [abs_of_neg (lt_of_not_ge h)] at hx
    have h2 : x^2 + x - 1 = 0 := by linarith

    have h3 : x^2 + x - 1 = (x - (-(1 : ℝ) + Real.sqrt 5) / 2) * (x - (-(1 : ℝ) - Real.sqrt 5) / 2) := by
      ring_nf
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      -- Verify the coefficients by comparing with the quadratic formula
      nlinarith

    rw [h3] at h2
    cases' (mul_eq_zero.mp h2) with h4 h5
    · -- Case where x = (-1 + sqrt(5))/2 (positive value, contradicts x < 0)
      have hx_eq : x = (-(1 : ℝ) + Real.sqrt 5) / 2 := by linarith
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

    · -- Case where x = (-1 - sqrt(5))/2 (negative)
      have hx_eq : x = (-(1 : ℝ) - Real.sqrt 5) / 2 := by linarith
      simp [hx_eq]
      <;> linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]