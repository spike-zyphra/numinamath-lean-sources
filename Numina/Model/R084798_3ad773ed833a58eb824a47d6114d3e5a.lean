import Mathlib

theorem algebra_195595 (x : ℝ) (hx : x^4 - 6 * x^3 + 7 * x^2 + 6 * x - 2 = 0)
    (hroots : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1^4 - 6 * x1^3 + 7 * x1^2 + 6 * x1 - 2 = 0 ∧
      x2^4 - 6 * x2^3 + 7 * x2^2 + 6 * x2 - 2 = 0 ∧ |x1 - x2| = 1) :
    x = 1 + Real.sqrt 3 ∨ x = 2 + Real.sqrt 3 ∨ x = 1 - Real.sqrt 3 ∨ x = 2 - Real.sqrt 3 := by

  have h1 : x^4 - 6 * x^3 + 7 * x^2 + 6 * x - 2 = (x^2 - 4 * x + 1) * (x^2 - 2 * x - 2) := by
    ring

  rw [h1] at hx

  cases' (mul_eq_zero.mp hx) with h2 h3

  · -- Case where $x^2 - 4x + 1 = 0$, solving this quadratic
    have h4 : x^2 - 4 * x + 1 = 0 := by linarith
    have h5 : x^2 - 4 * x + 1 = (x - (2 + Real.sqrt 3)) * (x - (2 - Real.sqrt 3)) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    
    rw [h5] at h4
    cases' (mul_eq_zero.mp h4) with h6 h7
  
    · -- Solving $x - (2 + \sqrt{3}) = 0$
      right
      left
      linarith
  
    · -- Solving $x - (2 - \sqrt{3}) = 0$
      right
      right
      right
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  
  · -- Case where $x^2 - 2x - 2 = 0$, solving this quadratic
    have h8 : x^2 - 2 * x - 2 = 0 := by linarith
    have h9 : x^2 - 2 * x - 2 = (x - (1 + Real.sqrt 3)) * (x - (1 - Real.sqrt 3)) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    
    rw [h9] at h8
    cases' (mul_eq_zero.mp h8) with h10 h11
  
    · -- Solving $x - (1 + \sqrt{3}) = 0$
      left
      linarith
  
    · -- Solving $x - (1 - \sqrt{3}) = 0$
      right
      right
      left
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]