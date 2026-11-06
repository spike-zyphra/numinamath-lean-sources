import Mathlib

theorem algebra_205714 (x : ℝ) (hx : x ≥ 1) :
    Real.sqrt (x - 1) * Real.sqrt (x + 1) = -Real.sqrt (x ^ 2 - 1) ↔ x = 1 := by
  constructor
  · -- Assume Real.sqrt (x - 1) * Real.sqrt (x + 1) = -Real.sqrt (x ^ 2 - 1) prove x = 1
    intro h
    have h1 : x - 1 ≥ 0 := by linarith
    have h2 : x + 1 ≥ 0 := by linarith
    have h3 : x ^ 2 - 1 ≥ 0 := by nlinarith
    have h4 : Real.sqrt (x - 1) * Real.sqrt (x + 1) = Real.sqrt (x ^ 2 - 1) := by
      have h5 : Real.sqrt (x - 1) * Real.sqrt (x + 1) = Real.sqrt ((x - 1) * (x + 1)) := by
        rw [← Real.sqrt_mul (by linarith)]
      have h6 : (x - 1 : ℝ) * (x + 1 : ℝ) = x ^ 2 - 1 := by
        ring_nf
      rw [h6] at h5
      linarith
    have h5 : Real.sqrt (x ^ 2 - 1) = -Real.sqrt (x ^ 2 - 1) := by
      linarith [h, h4]
    have h6 : Real.sqrt (x ^ 2 - 1) = 0 := by
      linarith [h5]
    have h7 : x ^ 2 - 1 = 0 := by
      rw [Real.sqrt_eq_zero (by nlinarith)] at h6
      linarith
    have h8 : x ^ 2 = 1 := by nlinarith
    have h9 : x = 1 := by nlinarith [sq_nonneg (x - 1)]
    exact h9
  · -- Assume x = 1 prove Real.sqrt (x - 1) * Real.sqrt (x + 1) = -Real.sqrt (x ^ 2 - 1)
    intro h
    rw [h]
    have h1 : Real.sqrt (1 - 1 : ℝ) = 0 := by
      norm_num [Real.sqrt_eq_zero]
    have h2 : Real.sqrt (1 + 1 : ℝ) = Real.sqrt 2 := by
      norm_num
    have h3 : Real.sqrt ((1 : ℝ) ^ 2 - 1) = 0 := by
      norm_num [Real.sqrt_eq_zero]
    rw [h1, h2, h3]
    all_goals norm_num