import Mathlib

theorem algebra_260912 (x : ℝ) (hx : x ≠ 0) (h : (x^2 - x + 1) * (3 * x^2 - 10 * x + 3) = 20 * x^2) :
    x = (5 + Real.sqrt 21) / 2 ∨ x = (5 - Real.sqrt 21) / 2 := by
  -- Equation to polynomial.
  have h1 : (x^2 - x + 1) * (3 * x^2 - 10 * x + 3) - 20 * x^2 = 0 := by linarith
  have h2 : (x ^ 2 - 5 * x + 1) * (3 * x ^ 2 + 2 * x + 3) = 0 := by
    nlinarith [h1]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Solve with real numbers
    have h5 : x ^ 2 - 5 * x + 1 = 0 := by 
      linarith
    have h6 : x ^ 2 - 5 * x + 1 = (x - (5 + Real.sqrt 21) / 2) * (x - (5 - Real.sqrt 21) / 2) := by
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      linarith [Real.sqrt_pos.mpr (by norm_num : (21 : ℝ) > 0)]
    rw [h6] at h5
    cases' (mul_eq_zero.mp h5) with h7 h8
    · left
      linarith
    · right
      linarith
  · -- Second equation in the system has no solutions
    exfalso
    have h5 : 3 * x ^ 2 + 2 * x + 3 > 0 := by
      nlinarith [sq_nonneg (x + 1 / 3)]
    have h6 : 3 * x ^ 2 + 2 * x + 3 = 0 := by 
      linarith [h4]
    nlinarith [h5, h6]