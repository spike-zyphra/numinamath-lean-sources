import Mathlib

theorem algebra_220750 (x : ℝ) : 16 * x ^ 2 + 2000 = 680 * x ↔
    x = (85 + 5 * Real.sqrt 209) / 4 ∨ x = (85 - 5 * Real.sqrt 209) / 4 := by 
  constructor
  · -- Forward direction: if the equation holds, then x is one of the two roots
    intro h
    have h1 : 16 * x^2 - 680 * x + 2000 = 0 := by linarith
    have h2 : (x - (85 + 5 * Real.sqrt 209) / 4) * (x - (85 - 5 * Real.sqrt 209) / 4) = 0 := by
      nlinarith [Real.sqrt_nonneg 209, Real.sq_sqrt (show (0 : ℝ) ≤ (209 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- First factor is zero
      left
      linarith
    · -- Second factor is zero
      right
      linarith
  · -- Backward direction: if x is one of the two roots, then the equation holds
    rintro (h | h)
    · -- First root
      rw [h]
      nlinarith [Real.sqrt_nonneg 209, Real.sq_sqrt (show (0 : ℝ) ≤ (209 : ℝ) by norm_num)]
    · -- Second root
      rw [h]
      nlinarith [Real.sqrt_nonneg 209, Real.sq_sqrt (show (0 : ℝ) ≤ (209 : ℝ) by norm_num)]