import Mathlib

open Real

theorem algebra_319215 (a b c r p : ℝ) (h0 : p * r > 1) (h1 : p * c - 2 * b + r * a = 0) :
    ∃ x : ℝ, a * x ^ 2 + 2 * b * x + c = 0 := by
  by_cases ha : a = 0
  · -- When a = 0, the quadratic reduces to a linear equation.
    rw [ha] at h1
    by_cases hb : b = 0
    · -- When a = 0 and b = 0, from h1: p * c = 0.
      rw [hb] at h1
      have hc : c = 0 := by
        have h2 : p * c = 0 := by linarith
        have hp1 : p ≠ 0 := by
          by_contra h
          rw [show p = 0 by linarith] at h0
          nlinarith
        have hc1 : c = 0 := by
          apply (mul_left_inj' hp1).mp 
          linarith
        linarith
      use 0
      simp [ha, hb, hc]
    · -- When a = 0 and b ≠ 0, solve the linear equation.
      use -c / (2 * b)
      field_simp [hb, ha]
      have h2 : p * c = 2 * b := by
        nlinarith
      nlinarith [sq_pos_of_pos (show 0 < p * r by linarith)]
  · -- When a ≠ 0.
    have h2 : (2 * b) ^ 2 - 4 * a * c ≥ 0 := by
      have h2b : (2 * b) ^ 2 = (p * c + r * a) ^ 2 := by
        have h : 2 * b = p * c + r * a := by 
          nlinarith [h1]
        rw [h]
      have h5 : (p * c + r * a) ^ 2 ≥ 4 * a * c := by
        have h5 : (p * c - r * a) ^ 2 ≥ 0 := sq_nonneg (p * c - r * a)
        nlinarith [sq_nonneg (c - a), sq_nonneg (p - r), sq_nonneg (p * c - r * a), sq_pos_of_pos (show 0 < p * r by linarith), sq_nonneg (a * c)]
      nlinarith [h2b, h5]
    use (-2 * b + Real.sqrt ((2 * b) ^ 2 - 4 * a * c)) / (2 * a)
    field_simp [show a ≠ 0 by exact ha]
    nlinarith [Real.sqrt_nonneg ((2 * b) ^ 2 - 4 * a * c), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * b) ^ 2 - 4 * a * c by linarith [h2])]